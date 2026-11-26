//! Deterministic Bit-Width, Operation, and Peak Memory Accounting (`BitLedger`).

#[derive(Clone, Debug, Default)]
pub struct BitLedger {
    pub max_int_bits: u32,
    pub max_float_exp: i32,
    pub min_float_nonzero_exp: i32,
    pub has_nonzero_float: bool,
    pub s_poly_reductions: u64,
    pub f2_xor_ops: u64,
    pub ldlt_ops: u64,
    pub fisher_rao_ops: u64,
    pub unit_prop_ops: u64,
    pub peak_memory_bytes: usize,
    pub current_memory_bytes: usize,
    pub overflow: bool,
    pub overflow_reason: Option<String>,
}

impl BitLedger {
    pub fn new() -> Self {
        Self {
            max_int_bits: 0,
            max_float_exp: i32::MIN,
            min_float_nonzero_exp: i32::MAX,
            has_nonzero_float: false,
            s_poly_reductions: 0,
            f2_xor_ops: 0,
            ldlt_ops: 0,
            fisher_rao_ops: 0,
            unit_prop_ops: 0,
            peak_memory_bytes: 0,
            current_memory_bytes: 0,
            overflow: false,
            overflow_reason: None,
        }
    }

    #[inline]
    pub fn record_int(&mut self, val: i64) {
        let abs = val.unsigned_abs();
        let bits = if abs == 0 { 0 } else { 64 - abs.leading_zeros() };
        if bits > self.max_int_bits {
            self.max_int_bits = bits;
        }
    }

    #[inline]
    pub fn record_u64(&mut self, val: u64) {
        let bits = if val == 0 { 0 } else { 64 - val.leading_zeros() };
        if bits > self.max_int_bits {
            self.max_int_bits = bits;
        }
    }

    #[inline]
    pub fn record_float(&mut self, val: f64) {
        if !val.is_finite() {
            self.overflow = true;
            if self.overflow_reason.is_none() {
                self.overflow_reason = Some(format!("non-finite float observed: {val}"));
            }
            return;
        }
        if val == 0.0 {
            return;
        }
        let bits = val.to_bits();
        let raw_exp = ((bits >> 52) & 0x7ff) as i32;
        let exp = if raw_exp == 0 {
            // Subnormal
            -1022
        } else {
            raw_exp - 1023
        };
        if !self.has_nonzero_float {
            self.has_nonzero_float = true;
            self.max_float_exp = exp;
            self.min_float_nonzero_exp = exp;
        } else {
            if exp > self.max_float_exp {
                self.max_float_exp = exp;
            }
            if exp < self.min_float_nonzero_exp {
                self.min_float_nonzero_exp = exp;
            }
        }
    }

    #[inline]
    pub fn record_mem_alloc(&mut self, bytes: usize) {
        self.current_memory_bytes = self.current_memory_bytes.saturating_add(bytes);
        if self.current_memory_bytes > self.peak_memory_bytes {
            self.peak_memory_bytes = self.current_memory_bytes;
        }
    }

    #[inline]
    pub fn record_mem_free(&mut self, bytes: usize) {
        self.current_memory_bytes = self.current_memory_bytes.saturating_sub(bytes);
    }

    #[inline]
    pub fn total_ops(&self) -> u64 {
        self.s_poly_reductions
            + self.f2_xor_ops
            + self.ldlt_ops
            + self.fisher_rao_ops
            + self.unit_prop_ops
    }

    pub fn effective_max_float_exp(&self) -> i32 {
        if self.has_nonzero_float {
            self.max_float_exp
        } else {
            0
        }
    }
}
