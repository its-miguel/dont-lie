//! Core Monotone 1-in-3 SAT instance and flat CSR incidence representation.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

#[derive(Clone, Debug)]
pub struct Instance {
    pub id: String,
    pub family: String,
    pub n_vars: usize,
    pub clauses: Vec<[usize; 3]>,
    pub ground_truth: String, // "SAT", "UNSAT", or "UNKNOWN"
}

impl Instance {
    pub fn m_clauses(&self) -> usize {
        self.clauses.len()
    }
}

/// Flat CSR variable-to-clause incidence structure for zero-allocation traversal.
#[derive(Clone, Debug)]
pub struct Incidence {
    pub n_vars: usize,
    pub m_clauses: usize,
    /// For each variable v, slice bounds into `var_clauses` are `var_offsets[v]..var_offsets[v+1]`.
    pub var_offsets: Vec<usize>,
    /// Pairs of (clause_idx, multiplicity in clause).
    pub var_clauses: Vec<(usize, u8)>,
    /// Variable degree (total literal occurrences).
    pub degrees: Vec<u32>,
}

impl Incidence {
    pub fn build(inst: &Instance) -> Self {
        let n = inst.n_vars;
        let m = inst.clauses.len();
        let mut counts = vec![0usize; n];
        let mut degrees = vec![0u32; n];

        for &[a, b, c] in &inst.clauses {
            degrees[a] += 1;
            degrees[b] += 1;
            degrees[c] += 1;
            counts[a] += 1;
            if b != a {
                counts[b] += 1;
            }
            if c != a && c != b {
                counts[c] += 1;
            }
        }

        let mut var_offsets = vec![0usize; n + 1];
        for v in 0..n {
            var_offsets[v + 1] = var_offsets[v] + counts[v];
        }

        let total_entries = var_offsets[n];
        let mut var_clauses = vec![(0usize, 0u8); total_entries];
        let mut cursor = var_offsets[..n].to_vec();

        for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
            if a == b && b == c {
                let pos = cursor[a];
                var_clauses[pos] = (c_idx, 3);
                cursor[a] += 1;
            } else if a == b {
                var_clauses[cursor[a]] = (c_idx, 2);
                cursor[a] += 1;
                var_clauses[cursor[c]] = (c_idx, 1);
                cursor[c] += 1;
            } else if a == c {
                var_clauses[cursor[a]] = (c_idx, 2);
                cursor[a] += 1;
                var_clauses[cursor[b]] = (c_idx, 1);
                cursor[b] += 1;
            } else if b == c {
                var_clauses[cursor[a]] = (c_idx, 1);
                cursor[a] += 1;
                var_clauses[cursor[b]] = (c_idx, 2);
                cursor[b] += 1;
            } else {
                var_clauses[cursor[a]] = (c_idx, 1);
                cursor[a] += 1;
                var_clauses[cursor[b]] = (c_idx, 1);
                cursor[b] += 1;
                var_clauses[cursor[c]] = (c_idx, 1);
                cursor[c] += 1;
            }
        }

        Self {
            n_vars: n,
            m_clauses: m,
            var_offsets,
            var_clauses,
            degrees,
        }
    }

    #[inline]
    pub fn clauses_of(&self, v: usize) -> &[(usize, u8)] {
        &self.var_clauses[self.var_offsets[v]..self.var_offsets[v + 1]]
    }
}

/// Load exported Python parity suite (`fixtures/python_suite_140.txt`).
pub fn load_parity_suite(path: &Path) -> std::io::Result<Vec<Instance>> {
    let file = File::open(path)?;
    let mut lines = BufReader::new(file).lines();
    let count: usize = lines
        .next()
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "empty fixture"))??
        .trim()
        .parse()
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

    let mut instances = Vec::with_capacity(count);
    for _ in 0..count {
        let header = lines
            .next()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "missing header"))??;
        let parts: Vec<&str> = header.split_whitespace().collect();
        if parts.len() != 5 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("bad header: {header}"),
            ));
        }
        let id = parts[0].to_string();
        let family = parts[1].to_string();
        let n_vars: usize = parts[2].parse().unwrap();
        let m_clauses: usize = parts[3].parse().unwrap();
        let ground_truth = parts[4].to_string();

        let mut clauses = Vec::with_capacity(m_clauses);
        for _ in 0..m_clauses {
            let cl = lines
                .next()
                .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "missing clause"))??;
            let nums: Vec<usize> = cl
                .split_whitespace()
                .map(|s| s.parse::<usize>().unwrap())
                .collect();
            clauses.push([nums[0], nums[1], nums[2]]);
        }
        instances.push(Instance {
            id,
            family,
            n_vars,
            clauses,
            ground_truth,
        });
    }
    Ok(instances)
}
