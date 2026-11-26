"""Bit-complexity instrumentation and tracked scalar arithmetic for PD-PFGC.

Tracks exact integer bit_length(), Fraction numerator/denominator bit-widths,
IEEE-754 float64 dynamic-range span ((max_exp - min_exp) + 53), cancellation loss,
Decimal physical bit-width, overflow/underflow/subnormal/NaN counters, and
per-iteration telemetry.
"""

from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction
import math
import sys
from typing import Any, Union

_FREXP = math.frexp
_ISFINITE = math.isfinite
_ISNAN = math.isnan
_FLOAT_MIN_NORMAL = sys.float_info.min  # 2**-1022
_LOG2_10 = math.log2(10.0)


class BitWidthExceededError(OverflowError):
    """Raised when an instrumented integer or rational scalar exceeds its configured bit guardrail."""


class BitLedger:
    """Per-run and per-iteration bit-width, dynamic-range, and operation telemetry."""

    __slots__ = (
        "max_int_bit_length",
        "max_signed_int_bits",
        "max_fraction_bits",
        "max_fraction_component_bits",
        "max_float_physical_bits",
        "max_float_exp",
        "min_float_nonzero_exp",
        "max_dynamic_range_bits",
        "max_cancellation_bits",
        "overflow_count",
        "underflow_to_zero_count",
        "subnormal_count",
        "nan_count",
        "int_ops",
        "float_ops",
        "fraction_ops",
        "decimal_ops",
        "max_int_bits_limit",
        "max_fraction_bits_limit",
        "raise_on_guardrail",
        "guardrail_tripped",
        "guardrail_reason",
        "iteration_bit_history",
        "_active_iter",
        "_iter_start_ops",
        "_iter_max_int_bits",
        "_iter_max_frac_bits",
        "_iter_max_exp",
        "_iter_min_exp",
        "_iter_sig_bits",
        "_iter_max_cancel",
    )

    def __init__(
        self,
        max_int_bits_limit: int | None = None,
        max_fraction_bits_limit: int | None = None,
        raise_on_guardrail: bool = True,
    ) -> None:
        self.max_int_bit_length: int = 0
        self.max_signed_int_bits: int = 0
        self.max_fraction_bits: int = 0
        self.max_fraction_component_bits: int = 0
        self.max_float_physical_bits: int = 0
        self.max_float_exp: int | None = None
        self.min_float_nonzero_exp: int | None = None
        self.max_dynamic_range_bits: int = 0
        self.max_cancellation_bits: int = 0

        self.overflow_count: int = 0
        self.underflow_to_zero_count: int = 0
        self.subnormal_count: int = 0
        self.nan_count: int = 0

        self.int_ops: int = 0
        self.float_ops: int = 0
        self.fraction_ops: int = 0
        self.decimal_ops: int = 0

        self.max_int_bits_limit = max_int_bits_limit
        self.max_fraction_bits_limit = max_fraction_bits_limit
        self.raise_on_guardrail = raise_on_guardrail
        self.guardrail_tripped: bool = False
        self.guardrail_reason: str = ""

        self.iteration_bit_history: list[dict[str, Any]] = []
        self._active_iter: int | None = None
        self._iter_start_ops: int = 0
        self._iter_max_int_bits: int = 0
        self._iter_max_frac_bits: int = 0
        self._iter_max_exp: int | None = None
        self._iter_min_exp: int | None = None
        self._iter_sig_bits: int = 0
        self._iter_max_cancel: int = 0

    def total_ops(self) -> int:
        return self.int_ops + self.float_ops + self.fraction_ops + self.decimal_ops

    def _trip_guardrail(self, reason: str) -> None:
        self.guardrail_tripped = True
        if not self.guardrail_reason:
            self.guardrail_reason = reason
        if self.raise_on_guardrail:
            raise BitWidthExceededError(reason)

    def record_int(self, val: int, count_op: bool = True) -> None:
        if count_op:
            self.int_ops += 1
        bits = abs(val).bit_length()
        if bits > self.max_int_bit_length:
            self.max_int_bit_length = bits
        signed_bits = bits + 1 if val != 0 else 1
        if signed_bits > self.max_signed_int_bits:
            self.max_signed_int_bits = signed_bits
        if bits > self._iter_max_int_bits:
            self._iter_max_int_bits = bits
        if self.max_int_bits_limit is not None and bits > self.max_int_bits_limit:
            self._trip_guardrail(
                f"Integer bit-length {bits} exceeded limit {self.max_int_bits_limit}"
            )

    def record_float(
        self,
        val: float,
        count_op: bool = True,
        cancellation_bits: int = 0,
        underflowed: bool = False,
    ) -> None:
        if count_op:
            self.float_ops += 1
        if self.max_float_physical_bits < 64:
            self.max_float_physical_bits = 64
        if 53 > self._iter_sig_bits:
            self._iter_sig_bits = 53
        if underflowed:
            self.underflow_to_zero_count += 1
        if not _ISFINITE(val):
            if _ISNAN(val):
                self.nan_count += 1
            else:
                self.overflow_count += 1
            return
        if val != 0.0:
            av = -val if val < 0.0 else val
            if av < _FLOAT_MIN_NORMAL:
                self.subnormal_count += 1
            _, exp = _FREXP(val)
            if self.max_float_exp is None or exp > self.max_float_exp:
                self.max_float_exp = exp
            if self.min_float_nonzero_exp is None or exp < self.min_float_nonzero_exp:
                self.min_float_nonzero_exp = exp
            span = (self.max_float_exp - self.min_float_nonzero_exp) + 53
            if span > self.max_dynamic_range_bits:
                self.max_dynamic_range_bits = span
            if self._iter_max_exp is None or exp > self._iter_max_exp:
                self._iter_max_exp = exp
            if self._iter_min_exp is None or exp < self._iter_min_exp:
                self._iter_min_exp = exp
        if cancellation_bits > self.max_cancellation_bits:
            self.max_cancellation_bits = cancellation_bits
        if cancellation_bits > self._iter_max_cancel:
            self._iter_max_cancel = cancellation_bits

    def record_fraction(self, val: Fraction, count_op: bool = True) -> None:
        if count_op:
            self.fraction_ops += 1
        nb = abs(val.numerator).bit_length()
        db = val.denominator.bit_length()
        total = nb + db
        comp = nb if nb >= db else db
        if total > self.max_fraction_bits:
            self.max_fraction_bits = total
        if comp > self.max_fraction_component_bits:
            self.max_fraction_component_bits = comp
        if comp > self.max_int_bit_length:
            self.max_int_bit_length = comp
        signed_comp = comp + 1 if val != 0 else 1
        if signed_comp > self.max_signed_int_bits:
            self.max_signed_int_bits = signed_comp
        if total > self._iter_max_frac_bits:
            self._iter_max_frac_bits = total
        if comp > self._iter_max_int_bits:
            self._iter_max_int_bits = comp
        if self.max_fraction_bits_limit is not None and total > self.max_fraction_bits_limit:
            self._trip_guardrail(
                f"Fraction bit-width {total} exceeded limit {self.max_fraction_bits_limit}"
            )
        if self.max_int_bits_limit is not None and comp > self.max_int_bits_limit:
            self._trip_guardrail(
                f"Fraction component bit-width {comp} exceeded int limit {self.max_int_bits_limit}"
            )

    def record_decimal(
        self,
        val: Decimal,
        ctx_prec: int,
        count_op: bool = True,
        cancellation_bits: int = 0,
    ) -> None:
        if count_op:
            self.decimal_ops += 1
        if not val.is_finite():
            if val.is_nan():
                self.nan_count += 1
            else:
                self.overflow_count += 1
            return
        # Approximate physical bit width for Decimal(prec=ctx_prec)
        sig_bits = math.ceil(ctx_prec * _LOG2_10)
        phys_bits = sig_bits + 16
        if phys_bits > self.max_float_physical_bits:
            self.max_float_physical_bits = phys_bits
        if sig_bits > self._iter_sig_bits:
            self._iter_sig_bits = sig_bits
        if val.is_subnormal():
            self.subnormal_count += 1
        if val != 0:
            # Binary exponent estimate from decimal adjusted exponent: val ~ 10^adj
            adj = val.adjusted()
            exp2 = math.ceil(adj * _LOG2_10) + 1
            if self.max_float_exp is None or exp2 > self.max_float_exp:
                self.max_float_exp = exp2
            if self.min_float_nonzero_exp is None or exp2 < self.min_float_nonzero_exp:
                self.min_float_nonzero_exp = exp2
            span = (self.max_float_exp - self.min_float_nonzero_exp) + sig_bits
            if span > self.max_dynamic_range_bits:
                self.max_dynamic_range_bits = span
            if self._iter_max_exp is None or exp2 > self._iter_max_exp:
                self._iter_max_exp = exp2
            if self._iter_min_exp is None or exp2 < self._iter_min_exp:
                self._iter_min_exp = exp2
        if cancellation_bits > self.max_cancellation_bits:
            self.max_cancellation_bits = cancellation_bits
        if cancellation_bits > self._iter_max_cancel:
            self._iter_max_cancel = cancellation_bits

    def begin_iteration(self, iter_idx: int) -> None:
        self._active_iter = iter_idx
        self._iter_start_ops = self.total_ops()
        self._iter_max_int_bits = 0
        self._iter_max_frac_bits = 0
        self._iter_max_exp = None
        self._iter_min_exp = None
        self._iter_sig_bits = 0
        self._iter_max_cancel = 0

    def end_iteration(self) -> dict[str, Any]:
        iter_span = 0
        if self._iter_max_exp is not None and self._iter_min_exp is not None:
            sig_bits = self._iter_sig_bits if self._iter_sig_bits > 0 else 53
            iter_span = (self._iter_max_exp - self._iter_min_exp) + sig_bits
        snap = {
            "iteration": self._active_iter,
            "iter_ops": self.total_ops() - self._iter_start_ops,
            "iter_max_int_bits": self._iter_max_int_bits,
            "iter_max_fraction_bits": self._iter_max_frac_bits,
            "iter_dynamic_range_bits": iter_span,
            "iter_max_cancellation_bits": self._iter_max_cancel,
            "cumulative_max_int_bits": self.max_int_bit_length,
            "cumulative_max_fraction_bits": self.max_fraction_bits,
            "cumulative_dynamic_range_bits": self.max_dynamic_range_bits,
        }
        self.iteration_bit_history.append(snap)
        self._active_iter = None
        return snap

    def summary(self) -> dict[str, Any]:
        return {
            "max_int_bit_length": self.max_int_bit_length,
            "max_signed_int_bits": self.max_signed_int_bits,
            "max_fraction_bits": self.max_fraction_bits,
            "max_fraction_component_bits": self.max_fraction_component_bits,
            "max_float_physical_bits": self.max_float_physical_bits,
            "max_float_exp": self.max_float_exp,
            "min_float_nonzero_exp": self.min_float_nonzero_exp,
            "max_dynamic_range_bits": self.max_dynamic_range_bits,
            "max_cancellation_bits": self.max_cancellation_bits,
            "overflow_count": self.overflow_count,
            "underflow_to_zero_count": self.underflow_to_zero_count,
            "subnormal_count": self.subnormal_count,
            "nan_count": self.nan_count,
            "int_ops": self.int_ops,
            "float_ops": self.float_ops,
            "fraction_ops": self.fraction_ops,
            "decimal_ops": self.decimal_ops,
            "total_ops": self.total_ops(),
            "guardrail_tripped": self.guardrail_tripped,
            "guardrail_reason": self.guardrail_reason,
        }


class TrackedInt:
    """Arbitrary-precision integer instrumented by a BitLedger."""

    __slots__ = ("value", "ledger")

    def __init__(self, value: int, ledger: BitLedger, count_op: bool = False) -> None:
        if isinstance(value, TrackedInt):
            value = value.value
        self.value: int = int(value)
        self.ledger: BitLedger = ledger
        ledger.record_int(self.value, count_op=count_op)

    def _raw(self, other: int | TrackedInt) -> int:
        return other.value if type(other) is TrackedInt else int(other)

    def __int__(self) -> int:
        return self.value

    def __float__(self) -> float:
        return float(self.value)

    def __abs__(self) -> TrackedInt:
        return TrackedInt(abs(self.value), self.ledger, count_op=True)

    def __neg__(self) -> TrackedInt:
        return TrackedInt(-self.value, self.ledger, count_op=True)

    def __pos__(self) -> TrackedInt:
        return TrackedInt(self.value, self.ledger, count_op=True)

    def __add__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value + self._raw(other), self.ledger, count_op=True)

    def __radd__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self._raw(other) + self.value, self.ledger, count_op=True)

    def __sub__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value - self._raw(other), self.ledger, count_op=True)

    def __rsub__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self._raw(other) - self.value, self.ledger, count_op=True)

    def __mul__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value * self._raw(other), self.ledger, count_op=True)

    def __rmul__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self._raw(other) * self.value, self.ledger, count_op=True)

    def __floordiv__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value // self._raw(other), self.ledger, count_op=True)

    def __rfloordiv__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self._raw(other) // self.value, self.ledger, count_op=True)

    def __mod__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value % self._raw(other), self.ledger, count_op=True)

    def __pow__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value ** self._raw(other), self.ledger, count_op=True)

    def __lshift__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value << self._raw(other), self.ledger, count_op=True)

    def __rshift__(self, other: int | TrackedInt) -> TrackedInt:
        return TrackedInt(self.value >> self._raw(other), self.ledger, count_op=True)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TrackedInt):
            return self.value == other.value
        if isinstance(other, int) and not isinstance(other, bool):
            return self.value == other
        return False

    def __lt__(self, other: int | TrackedInt) -> bool:
        return self.value < self._raw(other)

    def __le__(self, other: int | TrackedInt) -> bool:
        return self.value <= self._raw(other)

    def __gt__(self, other: int | TrackedInt) -> bool:
        return self.value > self._raw(other)

    def __ge__(self, other: int | TrackedInt) -> bool:
        return self.value >= self._raw(other)

    def __repr__(self) -> str:
        return f"TrackedInt({self.value})"


def _float_cancel_bits(a: float, b: float, r: float) -> int:
    if a == 0.0 or b == 0.0 or not (_ISFINITE(a) and _ISFINITE(b)):
        return 0
    if r == 0.0:
        return 53
    if not _ISFINITE(r):
        return 0
    _, ea = _FREXP(a)
    _, eb = _FREXP(b)
    _, er = _FREXP(r)
    mexp = ea if ea > eb else eb
    return (mexp - er) if mexp > er else 0


class TrackedFloat:
    """IEEE-754 float64 scalar instrumented by a BitLedger."""

    __slots__ = ("value", "ledger")

    def __init__(self, value: float, ledger: BitLedger, count_op: bool = False) -> None:
        if type(value) is TrackedFloat:
            v = value.value
        elif type(value) is TrackedInt:
            v = float(value.value)
        else:
            v = float(value)
        self.value: float = v
        self.ledger: BitLedger = ledger
        ledger.record_float(v, count_op=count_op)

    @staticmethod
    def _wrap(val: float, ledger: BitLedger, cancel: int = 0, underflow: bool = False) -> TrackedFloat:
        obj = object.__new__(TrackedFloat)
        obj.value = val
        obj.ledger = ledger
        ledger.record_float(val, count_op=True, cancellation_bits=cancel, underflowed=underflow)
        return obj

    def _raw(self, other: float | int | TrackedFloat | TrackedInt) -> float:
        t = type(other)
        if t is TrackedFloat:
            return other.value  # type: ignore[union-attr]
        if t is TrackedInt:
            return float(other.value)  # type: ignore[union-attr]
        return float(other)

    def __float__(self) -> float:
        return self.value

    def __abs__(self) -> TrackedFloat:
        return TrackedFloat._wrap(abs(self.value), self.ledger)

    def __neg__(self) -> TrackedFloat:
        return TrackedFloat._wrap(-self.value, self.ledger)

    def __pos__(self) -> TrackedFloat:
        return TrackedFloat._wrap(self.value, self.ledger)

    def __add__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self.value
        b = self._raw(other)
        r = a + b
        cancel = _float_cancel_bits(a, b, r)
        return TrackedFloat._wrap(r, self.ledger, cancel=cancel)

    def __radd__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        return self.__add__(other)

    def __sub__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self.value
        b = self._raw(other)
        r = a - b
        cancel = _float_cancel_bits(a, b, r)
        return TrackedFloat._wrap(r, self.ledger, cancel=cancel)

    def __rsub__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self._raw(other)
        b = self.value
        r = a - b
        cancel = _float_cancel_bits(a, b, r)
        return TrackedFloat._wrap(r, self.ledger, cancel=cancel)

    def __mul__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self.value
        b = self._raw(other)
        r = a * b
        uf = (r == 0.0 and a != 0.0 and b != 0.0)
        return TrackedFloat._wrap(r, self.ledger, underflow=uf)

    def __rmul__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        return self.__mul__(other)

    def __truediv__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self.value
        b = self._raw(other)
        r = a / b
        uf = (r == 0.0 and a != 0.0 and _ISFINITE(b))
        return TrackedFloat._wrap(r, self.ledger, underflow=uf)

    def __rtruediv__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self._raw(other)
        b = self.value
        r = a / b
        uf = (r == 0.0 and a != 0.0 and _ISFINITE(b))
        return TrackedFloat._wrap(r, self.ledger, underflow=uf)

    def __pow__(self, other: float | int | TrackedFloat | TrackedInt) -> TrackedFloat:
        a = self.value
        b = self._raw(other)
        r = a ** b
        uf = (r == 0.0 and a != 0.0)
        return TrackedFloat._wrap(r, self.ledger, underflow=uf)

    def __eq__(self, other: object) -> bool:
        if type(other) is TrackedFloat:
            return self.value == other.value
        if isinstance(other, (int, float)) and not isinstance(other, bool):
            return self.value == float(other)
        return False

    def __lt__(self, other: float | int | TrackedFloat | TrackedInt) -> bool:
        return self.value < self._raw(other)

    def __le__(self, other: float | int | TrackedFloat | TrackedInt) -> bool:
        return self.value <= self._raw(other)

    def __gt__(self, other: float | int | TrackedFloat | TrackedInt) -> bool:
        return self.value > self._raw(other)

    def __ge__(self, other: float | int | TrackedFloat | TrackedInt) -> bool:
        return self.value >= self._raw(other)

    def __repr__(self) -> str:
        return f"TrackedFloat({self.value!r})"


class TrackedFraction:
    """Exact rational scalar instrumented by a BitLedger."""

    __slots__ = ("value", "ledger")

    def __init__(
        self,
        value: Fraction | int | float | str | TrackedFraction,
        ledger: BitLedger,
        count_op: bool = False,
    ) -> None:
        if type(value) is TrackedFraction:
            v = value.value
        elif isinstance(value, Fraction):
            v = value
        elif isinstance(value, float):
            v = Fraction(value)
        else:
            v = Fraction(value)
        self.value: Fraction = v
        self.ledger: BitLedger = ledger
        ledger.record_fraction(v, count_op=count_op)

    def _raw(self, other: Fraction | int | float | TrackedFraction | TrackedInt) -> Fraction:
        t = type(other)
        if t is TrackedFraction:
            return other.value  # type: ignore[union-attr]
        if t is TrackedInt:
            return Fraction(other.value)  # type: ignore[union-attr]
        if isinstance(other, Fraction):
            return other
        return Fraction(other)

    def __float__(self) -> float:
        return float(self.value)

    def __abs__(self) -> TrackedFraction:
        return TrackedFraction(abs(self.value), self.ledger, count_op=True)

    def __neg__(self) -> TrackedFraction:
        return TrackedFraction(-self.value, self.ledger, count_op=True)

    def __pos__(self) -> TrackedFraction:
        return TrackedFraction(self.value, self.ledger, count_op=True)

    def __add__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self.value + self._raw(other), self.ledger, count_op=True)

    def __radd__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self._raw(other) + self.value, self.ledger, count_op=True)

    def __sub__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self.value - self._raw(other), self.ledger, count_op=True)

    def __rsub__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self._raw(other) - self.value, self.ledger, count_op=True)

    def __mul__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self.value * self._raw(other), self.ledger, count_op=True)

    def __rmul__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self._raw(other) * self.value, self.ledger, count_op=True)

    def __truediv__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self.value / self._raw(other), self.ledger, count_op=True)

    def __rtruediv__(self, other: Any) -> TrackedFraction:
        return TrackedFraction(self._raw(other) / self.value, self.ledger, count_op=True)

    def __pow__(self, other: int | TrackedInt) -> TrackedFraction:
        exp = other.value if type(other) is TrackedInt else int(other)
        return TrackedFraction(self.value ** exp, self.ledger, count_op=True)

    def __eq__(self, other: object) -> bool:
        if type(other) is TrackedFraction:
            return self.value == other.value
        if isinstance(other, (int, float, Fraction)) and not isinstance(other, bool):
            return self.value == Fraction(other)
        return False

    def __lt__(self, other: Any) -> bool:
        return self.value < self._raw(other)

    def __le__(self, other: Any) -> bool:
        return self.value <= self._raw(other)

    def __gt__(self, other: Any) -> bool:
        return self.value > self._raw(other)

    def __ge__(self, other: Any) -> bool:
        return self.value >= self._raw(other)

    def __repr__(self) -> str:
        return f"TrackedFraction({self.value!r})"


def _decimal_cancel_bits(a: Decimal, b: Decimal, r: Decimal, prec: int) -> int:
    if a == 0 or b == 0 or not (a.is_finite() and b.is_finite()):
        return 0
    if r == 0:
        return math.ceil(prec * _LOG2_10)
    if not r.is_finite():
        return 0
    ma = a.adjusted()
    mb = b.adjusted()
    mr = r.adjusted()
    madj = ma if ma > mb else mb
    if madj > mr:
        return math.ceil((madj - mr) * _LOG2_10)
    return 0


class TrackedDecimal:
    """High-precision Decimal scalar instrumented by a BitLedger."""

    __slots__ = ("value", "ledger", "prec")

    def __init__(
        self,
        value: Decimal | int | float | str | TrackedDecimal,
        ledger: BitLedger,
        prec: int = 80,
        count_op: bool = False,
    ) -> None:
        if type(value) is TrackedDecimal:
            v = value.value
            prec = value.prec if prec == 80 else prec
        elif isinstance(value, Decimal):
            v = value
        elif isinstance(value, float):
            v = Decimal(str(value))
        else:
            v = Decimal(value)
        self.value: Decimal = v
        self.ledger: BitLedger = ledger
        self.prec: int = prec
        ledger.record_decimal(v, ctx_prec=prec, count_op=count_op)

    def _raw(self, other: Any) -> Decimal:
        t = type(other)
        if t is TrackedDecimal:
            return other.value
        if t is TrackedInt:
            return Decimal(other.value)
        if isinstance(other, Decimal):
            return other
        if isinstance(other, float):
            return Decimal(str(other))
        return Decimal(other)

    def __float__(self) -> float:
        return float(self.value)

    def __abs__(self) -> TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = self.prec
            return TrackedDecimal(+abs(self.value), self.ledger, prec=self.prec, count_op=True)

    def __neg__(self) -> TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = self.prec
            return TrackedDecimal(-self.value, self.ledger, prec=self.prec, count_op=True)

    def __pos__(self) -> TrackedDecimal:
        return TrackedDecimal(self.value, self.ledger, prec=self.prec, count_op=True)

    @staticmethod
    def _wrap(
        val: Decimal,
        ledger: BitLedger,
        prec: int,
        cancel: int = 0,
    ) -> TrackedDecimal:
        obj = object.__new__(TrackedDecimal)
        obj.value = val
        obj.ledger = ledger
        obj.prec = prec
        ledger.record_decimal(val, ctx_prec=prec, count_op=True, cancellation_bits=cancel)
        return obj

    def __add__(self, other: Any) -> TrackedDecimal:
        a = self.value
        b = self._raw(other)
        with localcontext() as ctx:
            ctx.prec = self.prec
            r = a + b
        return TrackedDecimal._wrap(r, self.ledger, self.prec, cancel=_decimal_cancel_bits(a, b, r, self.prec))

    def __radd__(self, other: Any) -> TrackedDecimal:
        return self.__add__(other)

    def __sub__(self, other: Any) -> TrackedDecimal:
        a = self.value
        b = self._raw(other)
        with localcontext() as ctx:
            ctx.prec = self.prec
            r = a - b
        return TrackedDecimal._wrap(r, self.ledger, self.prec, cancel=_decimal_cancel_bits(a, b, r, self.prec))

    def __rsub__(self, other: Any) -> TrackedDecimal:
        a = self._raw(other)
        b = self.value
        with localcontext() as ctx:
            ctx.prec = self.prec
            r = a - b
        return TrackedDecimal._wrap(r, self.ledger, self.prec, cancel=_decimal_cancel_bits(a, b, r, self.prec))

    def __mul__(self, other: Any) -> TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = self.prec
            return TrackedDecimal(self.value * self._raw(other), self.ledger, prec=self.prec, count_op=True)

    def __rmul__(self, other: Any) -> TrackedDecimal:
        return self.__mul__(other)

    def __truediv__(self, other: Any) -> TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = self.prec
            return TrackedDecimal(self.value / self._raw(other), self.ledger, prec=self.prec, count_op=True)

    def __rtruediv__(self, other: Any) -> TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = self.prec
            return TrackedDecimal(self._raw(other) / self.value, self.ledger, prec=self.prec, count_op=True)

    def __pow__(self, other: Any) -> TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = self.prec
            return TrackedDecimal(self.value ** self._raw(other), self.ledger, prec=self.prec, count_op=True)

    def __eq__(self, other: object) -> bool:
        if type(other) is TrackedDecimal:
            return self.value == other.value
        if isinstance(other, (int, float, Decimal)) and not isinstance(other, bool):
            return self.value == self._raw(other)
        return False

    def __lt__(self, other: Any) -> bool:
        return self.value < self._raw(other)

    def __le__(self, other: Any) -> bool:
        return self.value <= self._raw(other)

    def __gt__(self, other: Any) -> bool:
        return self.value > self._raw(other)

    def __ge__(self, other: Any) -> bool:
        return self.value >= self._raw(other)

    def __repr__(self) -> str:
        return f"TrackedDecimal({self.value!r}, prec={self.prec})"


# ---------------------------------------------------------------------------
# High-precision Decimal & exact rational elementary math helpers
# ---------------------------------------------------------------------------

_DECIMAL_PI_CACHE: dict[int, Decimal] = {}


def _decimal_pi(prec: int) -> Decimal:
    """Compute pi to at least `prec` decimal digits using Machin's formula."""
    cached = _DECIMAL_PI_CACHE.get(prec)
    if cached is not None:
        return cached
    guard = prec + 12
    with localcontext() as ctx:
        ctx.prec = guard

        def arctan_inv(inv_x: int) -> Decimal:
            x2 = Decimal(inv_x * inv_x)
            term = Decimal(1) / Decimal(inv_x)
            total = term
            k = 1
            while True:
                term = -term / x2
                add = term / Decimal(2 * k + 1)
                if add == 0 or add.adjusted() < -guard:
                    break
                total += add
                k += 1
            return total

        pi_val = Decimal(4) * (Decimal(4) * arctan_inv(5) - arctan_inv(239))
    with localcontext() as ctx:
        ctx.prec = prec
        res = +pi_val
    _DECIMAL_PI_CACHE[prec] = res
    return res


def _decimal_cos(x: Decimal, prec: int) -> Decimal:
    guard = prec + 10
    pi_val = _decimal_pi(guard)
    two_pi = Decimal(2) * pi_val
    with localcontext() as ctx:
        ctx.prec = guard
        r = x % two_pi
        if r > pi_val:
            r -= two_pi
        r2 = r * r
        term = Decimal(1)
        total = term
        n = 1
        while True:
            term = -term * r2 / Decimal((2 * n - 1) * (2 * n))
            if term == 0 or term.adjusted() < -guard:
                break
            total += term
            n += 1
    with localcontext() as ctx:
        ctx.prec = prec
        return +total


def _decimal_sin(x: Decimal, prec: int) -> Decimal:
    guard = prec + 10
    pi_val = _decimal_pi(guard)
    two_pi = Decimal(2) * pi_val
    with localcontext() as ctx:
        ctx.prec = guard
        r = x % two_pi
        if r > pi_val:
            r -= two_pi
        r2 = r * r
        term = r
        total = term
        n = 1
        while True:
            term = -term * r2 / Decimal((2 * n) * (2 * n + 1))
            if term == 0 or term.adjusted() < -guard:
                break
            total += term
            n += 1
    with localcontext() as ctx:
        ctx.prec = prec
        return +total


def _fraction_pi() -> Fraction:
    # 25-digit rational approximation of pi for exact Fraction mode wrapping/beats
    return Fraction(3141592653589793238462643, 1000000000000000000000000)


def _fraction_cos(x: Fraction, order: int = 5) -> Fraction:
    # Range-reduce modulo 2*pi, then degree-(2*order) Taylor polynomial in pure Fraction arithmetic
    pi_q = _fraction_pi()
    two_pi = 2 * pi_q
    k = x // two_pi
    r = x - k * two_pi
    if r > pi_q:
        r -= two_pi
    elif r < -pi_q:
        r += two_pi
    r2 = r * r
    term = Fraction(1)
    total = term
    for n in range(1, order + 1):
        term = -term * r2 / ((2 * n - 1) * (2 * n))
        total += term
    return total


def _fraction_sin(x: Fraction, order: int = 5) -> Fraction:
    pi_q = _fraction_pi()
    two_pi = 2 * pi_q
    k = x // two_pi
    r = x - k * two_pi
    if r > pi_q:
        r -= two_pi
    elif r < -pi_q:
        r += two_pi
    r2 = r * r
    term = r
    total = term
    for n in range(1, order + 1):
        term = -term * r2 / ((2 * n) * (2 * n + 1))
        total += term
    return total


def _fraction_sqrt(x: Fraction, iters: int = 4) -> Fraction:
    if x < 0:
        raise ValueError("sqrt domain error for negative Fraction")
    if x == 0:
        return Fraction(0)
    num = x.numerator
    den = x.denominator
    bit_diff = num.bit_length() - den.bit_length()
    if bit_diff >= 106:
        g = Fraction(math.isqrt(num // den), 1)
    else:
        e = 54 - (bit_diff // 2)
        g = Fraction(math.isqrt((num << (2 * e)) // den), 1 << e)
    for _ in range(iters):
        g = (g + x / g) / 2
    return g


TrackedScalar = Union[TrackedFloat, TrackedFraction, TrackedDecimal]


def make_scalar(
    val: float | int | Fraction | Decimal,
    ledger: BitLedger,
    mode: str = "float64",
    decimal_prec: int = 80,
) -> TrackedScalar:
    if mode == "float64":
        return TrackedFloat(float(val), ledger, count_op=False)
    if mode == "fraction":
        return TrackedFraction(val, ledger, count_op=False)
    if mode == "decimal":
        return TrackedDecimal(val, ledger, prec=decimal_prec, count_op=False)
    raise ValueError(f"Unknown arithmetic mode: {mode!r}")


def t_pi(ledger: BitLedger, mode: str = "float64", decimal_prec: int = 80) -> TrackedScalar:
    if mode == "float64":
        return TrackedFloat(math.pi, ledger, count_op=False)
    if mode == "fraction":
        return TrackedFraction(_fraction_pi(), ledger, count_op=False)
    if mode == "decimal":
        return TrackedDecimal(_decimal_pi(decimal_prec), ledger, prec=decimal_prec, count_op=False)
    raise ValueError(f"Unknown arithmetic mode: {mode!r}")


def t_sin(x: TrackedScalar) -> TrackedScalar:
    t = type(x)
    if t is TrackedFloat:
        v = x.value
        r = math.sin(v)
        uf = (r == 0.0 and v != 0.0)
        return TrackedFloat._wrap(r, x.ledger, underflow=uf)
    if t is TrackedFraction:
        return TrackedFraction(_fraction_sin(x.value), x.ledger, count_op=True)
    if t is TrackedDecimal:
        return TrackedDecimal(_decimal_sin(x.value, x.prec), x.ledger, prec=x.prec, count_op=True)
    raise TypeError(f"Unsupported type for t_sin: {type(x).__name__}")


def t_cos(x: TrackedScalar) -> TrackedScalar:
    t = type(x)
    if t is TrackedFloat:
        return TrackedFloat._wrap(math.cos(x.value), x.ledger)
    if t is TrackedFraction:
        return TrackedFraction(_fraction_cos(x.value), x.ledger, count_op=True)
    if t is TrackedDecimal:
        return TrackedDecimal(_decimal_cos(x.value, x.prec), x.ledger, prec=x.prec, count_op=True)
    raise TypeError(f"Unsupported type for t_cos: {type(x).__name__}")


def t_sqrt(x: TrackedScalar) -> TrackedScalar:
    t = type(x)
    if t is TrackedFloat:
        return TrackedFloat._wrap(math.sqrt(x.value), x.ledger)
    if t is TrackedFraction:
        return TrackedFraction(_fraction_sqrt(x.value), x.ledger, count_op=True)
    if t is TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = x.prec
            return TrackedDecimal(x.value.sqrt(), x.ledger, prec=x.prec, count_op=True)
    raise TypeError(f"Unsupported type for t_sqrt: {type(x).__name__}")


def t_exp(x: TrackedScalar) -> TrackedScalar:
    t = type(x)
    if t is TrackedFloat:
        v = x.value
        try:
            r = math.exp(v)
        except OverflowError:
            r = math.inf
        uf = (r == 0.0)
        return TrackedFloat._wrap(r, x.ledger, underflow=uf)
    if t is TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = x.prec
            return TrackedDecimal(x.value.exp(), x.ledger, prec=x.prec, count_op=True)
    if t is TrackedFraction:
        v = x.value
        if v <= -746:
            x.ledger.underflow_to_zero_count += 1
            return TrackedFraction(Fraction(0), x.ledger, count_op=True)
        if v > 709:
            if v <= 710:
                try:
                    return TrackedFraction(math.exp(float(v)), x.ledger, count_op=True)
                except OverflowError:
                    pass
            x.ledger.overflow_count += 1
            return TrackedFraction(Fraction(math.exp(709.0)), x.ledger, count_op=True)
        r = math.exp(float(v))
        if r == 0.0:
            x.ledger.underflow_to_zero_count += 1
        return TrackedFraction(r, x.ledger, count_op=True)
    raise TypeError(f"Unsupported type for t_exp: {type(x).__name__}")


def t_log(x: TrackedScalar) -> TrackedScalar:
    t = type(x)
    if t is TrackedFloat:
        return TrackedFloat._wrap(math.log(x.value), x.ledger)
    if t is TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = x.prec
            return TrackedDecimal(x.value.ln(), x.ledger, prec=x.prec, count_op=True)
    if t is TrackedFraction:
        v = x.value
        if v <= 0:
            raise ValueError("math domain error")
        shift = v.numerator.bit_length() - v.denominator.bit_length()
        if -900 <= shift <= 900:
            return TrackedFraction(math.log(float(v)), x.ledger, count_op=True)
        if shift >= 0:
            m = Fraction(v.numerator, v.denominator << shift)
        else:
            m = Fraction(v.numerator << (-shift), v.denominator)
        return TrackedFraction(math.log(float(m)) + shift * math.log(2.0), x.ledger, count_op=True)
    raise TypeError(f"Unsupported type for t_log: {type(x).__name__}")


def t_acos(x: TrackedScalar) -> TrackedScalar:
    t = type(x)
    if t is TrackedFloat:
        return TrackedFloat._wrap(math.acos(x.value), x.ledger)
    if t is TrackedDecimal:
        # Compute acos via float initial guess + Newton on cos(theta) = x
        val = x.value
        if val >= 1:
            return TrackedDecimal(Decimal(0), x.ledger, prec=x.prec, count_op=True)
        if val <= -1:
            return TrackedDecimal(_decimal_pi(x.prec), x.ledger, prec=x.prec, count_op=True)
        theta = Decimal(str(math.acos(max(-1.0, min(1.0, float(val))))))
        with localcontext() as ctx:
            ctx.prec = x.prec + 6
            for _ in range(5):
                s = _decimal_sin(theta, x.prec + 6)
                c = _decimal_cos(theta, x.prec + 6)
                if s == 0:
                    break
                theta = theta + (c - val) / s
        with localcontext() as ctx:
            ctx.prec = x.prec
            return TrackedDecimal(+theta, x.ledger, prec=x.prec, count_op=True)
    if t is TrackedFraction:
        v = x.value
        if v >= 1:
            return TrackedFraction(Fraction(0), x.ledger, count_op=True)
        if v <= -1:
            return TrackedFraction(_fraction_pi(), x.ledger, count_op=True)
        return TrackedFraction(math.acos(max(-1.0, min(1.0, float(v)))), x.ledger, count_op=True)
    raise TypeError(f"Unsupported type for t_acos: {type(x).__name__}")


def t_fmod_2pi(phi: TrackedScalar, mode: str = "float64", decimal_prec: int = 80) -> TrackedScalar:
    """Wrap angle phi into (-pi, pi] using tracked arithmetic."""
    pi_s = t_pi(phi.ledger, mode=mode, decimal_prec=decimal_prec)
    two_pi = pi_s + pi_s
    if type(phi) is TrackedFloat:
        v = ((phi.value + pi_s.value) % two_pi.value) - pi_s.value
        if v <= -pi_s.value:
            v += two_pi.value
        return TrackedFloat._wrap(v, phi.ledger)
    if type(phi) is TrackedDecimal:
        with localcontext() as ctx:
            ctx.prec = phi.prec
            v = ((phi.value + pi_s.value) % two_pi.value) - pi_s.value
            if v <= -pi_s.value:
                v += two_pi.value
            return TrackedDecimal(v, phi.ledger, prec=phi.prec, count_op=True)
    if type(phi) is TrackedFraction:
        k = (phi.value + pi_s.value) // two_pi.value
        v = phi.value - k * two_pi.value
        if v <= -pi_s.value:
            v += two_pi.value
        return TrackedFraction(v, phi.ledger, count_op=True)
    raise TypeError(f"Unsupported type for t_fmod_2pi: {type(phi).__name__}")
