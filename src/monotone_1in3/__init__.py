"""PD-PFGC constructive solver and empirical evaluation package for Monotone 1-in-3 SAT."""

from .bitwidth import (
    BitLedger,
    BitWidthExceededError,
    TrackedDecimal,
    TrackedFloat,
    TrackedFraction,
    TrackedInt,
)
from .instance import Monotone1in3Instance, SparseIncidence, build_incidence
from .solver import SolverConfig, SolverResult, solve_pd_pfgc
from .verifier import VerificationResult, verify_assignment, verify_raw

__all__ = [
    "BitLedger",
    "BitWidthExceededError",
    "Monotone1in3Instance",
    "SolverConfig",
    "SolverResult",
    "SparseIncidence",
    "TrackedDecimal",
    "TrackedFloat",
    "TrackedFraction",
    "TrackedInt",
    "VerificationResult",
    "build_incidence",
    "solve_pd_pfgc",
    "verify_assignment",
    "verify_raw",
]
