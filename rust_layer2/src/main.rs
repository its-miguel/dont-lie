//! CLI runner comparing Layer 2 (`HybridGroebnerCascade`) vs Layer 2.5 (`GadgetSPCascade`)
//! vs Layer 2.75 (`GadgetSPCascade` + Bounded Z-Cutting-Planes) across the 140-instance
//! Python parity suite and the 72-instance high-scale suite (n = 150, 300, 600).

use std::collections::BTreeMap;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use monotone_1in3_layer2::diagnostic::profile_frontier_instance;
use monotone_1in3_layer2::generators::{
    gen_f1_random_crit, gen_f3_tseitin_expander, gen_f4_3sat_high_girth, gen_f5_pigeonhole,
    gen_f6_hybrid_f2_z_trap, generate_f6_suite, generate_layer2_suite,
};
use monotone_1in3_layer2::instance::{load_parity_suite, Instance};
use monotone_1in3_layer2::solver::{HybridGroebnerCascade, SolveOutcome, SolveResult};
use monotone_1in3_layer2::solver_v25::GadgetSPCascade;
use monotone_1in3_layer2::verifier::export_lean_certificate;

struct Row {
    solver_name: String,
    suite: String,
    target_n: usize,
    inst: Instance,
    res: SolveResult,
    false_sat: bool,
    false_unsat: bool,
}

#[derive(Default)]
struct Bucket {
    total: usize,
    vsat: usize,
    vunsat: usize,
    unres: usize,
    ovf: usize,
    fsat: usize,
    funsat: usize,
    sum_n: f64,
    sum_ops: f64,
    sum_time: f64,
    max_int_bits: u32,
    max_float_exp: i32,
    max_mem: usize,
}

fn outcome_str(o: SolveOutcome) -> &'static str {
    match o {
        SolveOutcome::VerifiedSat => "VERIFIED_SAT",
        SolveOutcome::VerifiedUnsat => "VERIFIED_UNSAT",
        SolveOutcome::Unresolved => "UNRESOLVED",
        SolveOutcome::Overflow => "OVERFLOW",
    }
}

fn aggregate(rows: &[Row]) -> BTreeMap<(String, usize), Bucket> {
    let mut buckets: BTreeMap<(String, usize), Bucket> = BTreeMap::new();
    for r in rows {
        let b = buckets
            .entry((r.inst.family.clone(), r.target_n))
            .or_default();
        b.total += 1;
        match r.res.outcome {
            SolveOutcome::VerifiedSat => b.vsat += 1,
            SolveOutcome::VerifiedUnsat => b.vunsat += 1,
            SolveOutcome::Unresolved => b.unres += 1,
            SolveOutcome::Overflow => b.ovf += 1,
        }
        if r.false_sat {
            b.fsat += 1;
        }
        if r.false_unsat {
            b.funsat += 1;
        }
        b.sum_n += r.inst.n_vars as f64;
        b.sum_ops += r.res.ledger.total_ops() as f64;
        b.sum_time += r.res.runtime_sec;
        b.max_int_bits = b.max_int_bits.max(r.res.ledger.max_int_bits);
        if b.total == 1 {
            b.max_float_exp = r.res.ledger.effective_max_float_exp();
        } else {
            b.max_float_exp = b.max_float_exp.max(r.res.ledger.effective_max_float_exp());
        }
        b.max_mem = b.max_mem.max(r.res.ledger.peak_memory_bytes);
    }
    buckets
}

fn run_parity_suite<F>(name: &str, cases: &[Instance], solve_fn: F) -> (usize, usize, usize, usize, usize, usize, f64)
where
    F: Fn(&Instance) -> SolveResult,
{
    let (mut sat, mut unsat, mut unres, mut fsat, mut funsat, mut ovf) = (0, 0, 0, 0, 0, 0);
    let mut t_sum = 0.0;
    for inst in cases {
        let res = solve_fn(inst);
        match res.outcome {
            SolveOutcome::VerifiedSat => {
                sat += 1;
                if inst.ground_truth == "UNSAT" {
                    fsat += 1;
                }
            }
            SolveOutcome::VerifiedUnsat => {
                unsat += 1;
                if inst.ground_truth == "SAT" {
                    funsat += 1;
                }
            }
            SolveOutcome::Unresolved => unres += 1,
            SolveOutcome::Overflow => ovf += 1,
        }
        t_sum += res.runtime_sec;
    }
    println!(
        "[PARITY 140 | {name}] VERIFIED_SAT={sat}/101 VERIFIED_UNSAT={unsat}/39 UNRESOLVED={unres} FALSE_SAT={fsat} FALSE_UNSAT={funsat} OVERFLOW={ovf} TIME={t_sum:.4}s"
    );
    (sat, unsat, unres, fsat, funsat, ovf, t_sum)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--diagnose-frontier") {
        let frontier = vec![
            gen_f4_3sat_high_girth(300, 20304511),
            gen_f4_3sat_high_girth(300, 20305520),
            gen_f1_random_crit(600, 20310565),
            gen_f4_3sat_high_girth(600, 20328727),
            gen_f4_3sat_high_girth(600, 20329736),
        ];
        println!(
            "{:<34} | {:<6} | {:<10} | {:<7} | {:<7} | {:<7} | {:<8} | {:<6} | {:<6}",
            "Instance", "GT", "Nodes", "Time(s)", "Fix%", "Froz%", "Water%", "AvgDep", "UniqC"
        );
        for inst in &frontier {
            let d = profile_frontier_instance(inst);
            println!(
                "{:<34} | {:<6} | {:<10} | {:<7.4} | {:<7.1} | {:<7.1} | {:<8.1} | {:<6.1} | {:<6}",
                d.instance_id,
                d.ground_truth,
                d.oracle_nodes,
                d.oracle_time_sec,
                100.0 * d.root_fixed_frac,
                100.0 * d.root_sp_frozen_frac,
                100.0 * d.root_sp_water_frac,
                d.avg_depth_before_conflict,
                d.unique_conflict_vars
            );
        }
        return;
    }

    if args.iter().any(|a| a == "--benchmark-f6") {
        let l2_solver = HybridGroebnerCascade::default();
        let l25_solver = GadgetSPCascade::default();
        let l275_solver = GadgetSPCascade::layer275();
        let l28_solver = GadgetSPCascade::layer28();
        let f6_cases = generate_f6_suite(20261125);

        println!(
            "{:<38} | {:<4} | {:<5} | {:<14} | {:<14} | {:<14} | {:<14} | {:<7} | {:<4}",
            "Instance", "n", "GT", "Layer 2", "Layer 2.5", "Layer 2.75", "Layer 2.8", "L2.8(s)", "Bits"
        );
        let mut csv = File::create(Path::new("../reports/f6_hybrid_results.csv")).unwrap();
        writeln!(
            csv,
            "solver,instance_id,family,target_n,n_vars,m_clauses,ground_truth,outcome,false_sat,false_unsat,termination_reason,unsat_cert_steps,runtime_sec,total_ops,max_int_bits,max_float_exp,peak_memory_bytes"
        )
        .unwrap();

        for (target_n, inst) in &f6_cases {
            let r2 = l2_solver.solve(inst);
            let r25 = l25_solver.solve(inst);
            let r275 = l275_solver.solve(inst);
            let r28 = l28_solver.solve(inst);
            println!(
                "{:<38} | {:<4} | {:<5} | {:<14} | {:<14} | {:<14} | {:<14} | {:<7.4} | {:<4}",
                inst.id,
                inst.n_vars,
                inst.ground_truth,
                outcome_str(r2.outcome),
                outcome_str(r25.outcome),
                outcome_str(r275.outcome),
                outcome_str(r28.outcome),
                r28.runtime_sec,
                r28.ledger.max_int_bits,
            );
            for (sname, r) in [
                ("Layer2", &r2),
                ("Layer2.5", &r25),
                ("Layer2.75", &r275),
                ("Layer2.8", &r28),
            ] {
                let fs = r.outcome == SolveOutcome::VerifiedSat && inst.ground_truth == "UNSAT";
                let fu = r.outcome == SolveOutcome::VerifiedUnsat && inst.ground_truth == "SAT";
                writeln!(
                    csv,
                    "{},{},{},{},{},{},{},{},{},{},{},{},{:.6},{},{},{},{}",
                    sname,
                    inst.id,
                    inst.family,
                    target_n,
                    inst.n_vars,
                    inst.m_clauses(),
                    inst.ground_truth,
                    outcome_str(r.outcome),
                    fs,
                    fu,
                    r.termination_reason,
                    r.unsat_cert_steps,
                    r.runtime_sec,
                    r.ledger.total_ops(),
                    r.ledger.max_int_bits,
                    r.ledger.effective_max_float_exp(),
                    r.ledger.peak_memory_bytes,
                )
                .unwrap();
            }
        }
        return;
    }

    if args.iter().any(|a| a == "--export-f6-cert") {
        let mut solver = GadgetSPCascade::layer275();
        solver.s_poly_factor = 0;
        let out_dir = Path::new("../lean4_layer3/Monotone1in3Layer3/GeneratedCerts");
        let inst = gen_f6_hybrid_f2_z_trap(600, false, 20261125 + 1009 * 13);
        let t0 = std::time::Instant::now();
        let res = solver.solve(&inst);
        assert_eq!(
            res.outcome,
            SolveOutcome::VerifiedUnsat,
            "expected VerifiedUnsat for {}, got {:?} ({})",
            inst.id,
            res.outcome,
            res.termination_reason
        );
        let cert = res.unsat_cert.as_ref().expect("missing unsat_cert");
        let path = out_dir.join("HybridF2Z600Cert.lean");
        let (raw_steps, pruned_steps) =
            export_lean_certificate("HybridF2Z600Cert", &inst, cert, &path).expect("export failed");
        println!(
            "[EXPORT F6] HybridF2Z600Cert ({}): n={} m={} raw_steps={} pruned_steps={} total_time={:.4}s -> {}",
            inst.id,
            inst.n_vars,
            inst.m_clauses(),
            raw_steps,
            pruned_steps,
            t0.elapsed().as_secs_f64(),
            path.display()
        );
        return;
    }

    if args.iter().any(|a| a == "--export-benchmarks") {
        let base_dir = Path::new("../benchmarks");
        let cnf_dir = base_dir.join("dimacs");
        let opb_dir = base_dir.join("opb");
        std::fs::create_dir_all(&cnf_dir).expect("mkdir dimacs");
        std::fs::create_dir_all(&opb_dir).expect("mkdir opb");

        let mut all_cases: Vec<(&str, usize, Instance)> = Vec::new();
        for (tn, inst) in generate_layer2_suite(20261124) {
            all_cases.push(("high_scale_72", tn, inst));
        }
        for (tn, inst) in generate_f6_suite(20261125) {
            all_cases.push(("f6_hybrid_18", tn, inst));
        }

        let mut manifest = File::create(base_dir.join("manifest.csv")).expect("create manifest");
        writeln!(manifest, "suite,instance_id,family,target_n,n_vars,m_clauses,ground_truth,cnf_path,opb_path").unwrap();

        for (suite, tn, inst) in &all_cases {
            let cnf_path = cnf_dir.join(format!("{}.cnf", inst.id));
            let opb_path = opb_dir.join(format!("{}.opb", inst.id));

            // Exact DIMACS CNF encoding of Monotone 1-in-3 SAT:
            // For each clause (a, b, c) with 1-based vars (A, B, C):
            //   (A v B v C) and pairwise (-A v -B), (-B v -C), (-A v -C) (deduping identical vars)
            let mut cnf_clauses: Vec<Vec<i64>> = Vec::with_capacity(inst.m_clauses() * 4);
            for &[a, b, c] in &inst.clauses {
                let va = (a + 1) as i64;
                let vb = (b + 1) as i64;
                let vc = (c + 1) as i64;
                // Positive disjunction
                let mut pos = vec![va, vb, vc];
                pos.sort_unstable();
                pos.dedup();
                cnf_clauses.push(pos);
                // Pairwise at-most-one: if two slots are identical (e.g. a == b), force -a!
                let slots = [va, vb, vc];
                for i in 0..3 {
                    for j in (i + 1)..3 {
                        if slots[i] == slots[j] {
                            cnf_clauses.push(vec![-slots[i]]);
                        } else {
                            cnf_clauses.push(vec![-slots[i], -slots[j]]);
                        }
                    }
                }
            }
            let mut cf = File::create(&cnf_path).expect("create cnf");
            writeln!(cf, "c Monotone 1-in-3 SAT exact CNF: {}", inst.id).unwrap();
            writeln!(cf, "p cnf {} {}", inst.n_vars, cnf_clauses.len()).unwrap();
            for cl in &cnf_clauses {
                for lit in cl {
                    write!(cf, "{lit} ").unwrap();
                }
                writeln!(cf, "0").unwrap();
            }

            // Exact OPB encoding: +1 xA +1 xB +1 xC = 1 ;
            // Combine duplicate variables in a clause cleanly (e.g., (a, a, b) -> +2 xA +1 xB = 1 ;)
            let mut of = File::create(&opb_path).expect("create opb");
            writeln!(of, "* #variable= {} #constraint= {}", inst.n_vars, inst.m_clauses()).unwrap();
            for &[a, b, c] in &inst.clauses {
                let mut counts: BTreeMap<usize, i64> = BTreeMap::new();
                *counts.entry(a + 1).or_insert(0) += 1;
                *counts.entry(b + 1).or_insert(0) += 1;
                *counts.entry(c + 1).or_insert(0) += 1;
                for (v, coeff) in counts {
                    write!(of, "+{coeff} x{v} ").unwrap();
                }
                writeln!(of, "= 1 ;").unwrap();
            }

            writeln!(
                manifest,
                "{},{},{},{},{},{},{},{},{}",
                suite,
                inst.id,
                inst.family,
                tn,
                inst.n_vars,
                inst.m_clauses(),
                inst.ground_truth,
                cnf_path.display(),
                opb_path.display()
            )
            .unwrap();
        }
        println!("[EXPORT BENCHMARKS] Exported {} instances to ../benchmarks/{{dimacs,opb}}", all_cases.len());
        return;
    }

    if args.iter().any(|a| a == "--frontier-l28") {
        let solver = GadgetSPCascade::layer28();
        let frontier = vec![
            gen_f4_3sat_high_girth(300, 20304511),
            gen_f4_3sat_high_girth(300, 20305520),
            gen_f1_random_crit(600, 20310565),
            gen_f4_3sat_high_girth(600, 20328727),
            gen_f4_3sat_high_girth(600, 20329736),
        ];
        for inst in &frontier {
            let res = solver.solve(inst);
            println!(
                "  [L2.8 FRONTIER] {:<34} n={:<4} m={:<4} => {:<14} steps={:<6} ops={:<9} bits={:<2} t={:.4}s ({})",
                inst.id,
                inst.n_vars,
                inst.m_clauses(),
                outcome_str(res.outcome),
                res.unsat_cert_steps,
                res.ledger.total_ops(),
                res.ledger.max_int_bits,
                res.runtime_sec,
                res.termination_reason,
            );
        }
        return;
    }

    if args.iter().any(|a| a == "--export-cert") {
        let solver = GadgetSPCascade::layer275();
        let out_dir = Path::new("../lean4_layer3/Monotone1in3Layer3/GeneratedCerts");

        let targets = [
            (
                "Tseitin610Cert",
                gen_f3_tseitin_expander(600, false, 20324691),
                out_dir.join("Tseitin610Cert.lean"),
            ),
            (
                "Pigeonhole637Cert",
                gen_f5_pigeonhole(600, 20332763),
                out_dir.join("Pigeonhole637Cert.lean"),
            ),
        ];

        for (ns, inst, path) in targets {
            let t0 = std::time::Instant::now();
            let res = solver.solve(&inst);
            assert_eq!(
                res.outcome,
                SolveOutcome::VerifiedUnsat,
                "expected VerifiedUnsat for {}, got {:?} ({})",
                inst.id,
                res.outcome,
                res.termination_reason
            );
            let cert = res.unsat_cert.as_ref().expect("missing unsat_cert");
            let (raw_steps, pruned_steps) =
                export_lean_certificate(ns, &inst, cert, &path).expect("export failed");
            let dt = t0.elapsed().as_secs_f64();
            println!(
                "[EXPORT] {} ({}): n={} m={} raw_steps={} pruned_steps={} total_time={:.4}s -> {}",
                ns,
                inst.id,
                inst.n_vars,
                inst.m_clauses(),
                raw_steps,
                pruned_steps,
                dt,
                path.display()
            );
        }
        return;
    }

    let l2_solver = HybridGroebnerCascade::default();
    let l25_solver = GadgetSPCascade::default();
    let l275_solver = GadgetSPCascade::layer275();
    let l28_solver = GadgetSPCascade::layer28();

    // 1. Parity Suite (140 instances, n = 15, 30, 60)
    let parity_cases =
        load_parity_suite(Path::new("fixtures/python_suite_140.txt")).expect("load parity fixture");
    let p_l2 = run_parity_suite("Layer 2 (HybridGroebnerCascade)", &parity_cases, |i| {
        l2_solver.solve(i)
    });
    let p_l25 = run_parity_suite("Layer 2.5 (GadgetSPCascade)", &parity_cases, |i| {
        l25_solver.solve(i)
    });
    let p_l275 = run_parity_suite("Layer 2.75 (GadgetSP+CuttingPlanes)", &parity_cases, |i| {
        l275_solver.solve(i)
    });
    let p_l28 = run_parity_suite("Layer 2.8 (GadgetSP+CP+FLP+Nogoods)", &parity_cases, |i| {
        l28_solver.solve(i)
    });

    // 2. High-Scale Adversarial Suite (72 instances, n = 150, 300, 600)
    let layer2_cases = generate_layer2_suite(20261124);
    let mut rows_l2: Vec<Row> = Vec::with_capacity(layer2_cases.len());
    let mut rows_l25: Vec<Row> = Vec::with_capacity(layer2_cases.len());
    let mut rows_l275: Vec<Row> = Vec::with_capacity(layer2_cases.len());
    let mut rows_l28: Vec<Row> = Vec::with_capacity(layer2_cases.len());

    let (mut t_l2, mut t_l25, mut t_l275, mut t_l28) = (0.0, 0.0, 0.0, 0.0);
    for (target_n, inst) in &layer2_cases {
        let r2 = l2_solver.solve(inst);
        t_l2 += r2.runtime_sec;
        rows_l2.push(Row {
            solver_name: "Layer2_HybridGroebnerCascade".to_string(),
            suite: "layer2_high_scale".to_string(),
            target_n: *target_n,
            inst: inst.clone(),
            false_sat: r2.outcome == SolveOutcome::VerifiedSat && inst.ground_truth == "UNSAT",
            false_unsat: r2.outcome == SolveOutcome::VerifiedUnsat && inst.ground_truth == "SAT",
            res: r2,
        });

        let r25 = l25_solver.solve(inst);
        t_l25 += r25.runtime_sec;
        rows_l25.push(Row {
            solver_name: "Layer2.5_GadgetSPCascade".to_string(),
            suite: "layer2_high_scale".to_string(),
            target_n: *target_n,
            inst: inst.clone(),
            false_sat: r25.outcome == SolveOutcome::VerifiedSat && inst.ground_truth == "UNSAT",
            false_unsat: r25.outcome == SolveOutcome::VerifiedUnsat && inst.ground_truth == "SAT",
            res: r25,
        });

        let r275 = l275_solver.solve(inst);
        t_l275 += r275.runtime_sec;
        rows_l275.push(Row {
            solver_name: "Layer2.75_GadgetSP_CuttingPlanes".to_string(),
            suite: "layer2_high_scale".to_string(),
            target_n: *target_n,
            inst: inst.clone(),
            false_sat: r275.outcome == SolveOutcome::VerifiedSat && inst.ground_truth == "UNSAT",
            false_unsat: r275.outcome == SolveOutcome::VerifiedUnsat && inst.ground_truth == "SAT",
            res: r275,
        });

        let r28 = l28_solver.solve(inst);
        t_l28 += r28.runtime_sec;
        println!(
            "  [L2.8]  {:<34} n={:<4} => {:<14} ops={:<9} bits={:<2} t={:.4}s ({})",
            inst.id,
            inst.n_vars,
            outcome_str(r28.outcome),
            r28.ledger.total_ops(),
            r28.ledger.max_int_bits,
            r28.runtime_sec,
            r28.termination_reason,
        );
        rows_l28.push(Row {
            solver_name: "Layer2.8_GadgetSP_CP_FLP_Nogoods".to_string(),
            suite: "layer2_high_scale".to_string(),
            target_n: *target_n,
            inst: inst.clone(),
            false_sat: r28.outcome == SolveOutcome::VerifiedSat && inst.ground_truth == "UNSAT",
            false_unsat: r28.outcome == SolveOutcome::VerifiedUnsat && inst.ground_truth == "SAT",
            res: r28,
        });
    }

    println!(
        "[HIGH-SCALE 72] Layer 2: {:.3}s | Layer 2.5: {:.3}s | Layer 2.75: {:.3}s | Layer 2.8: {:.3}s",
        t_l2, t_l25, t_l275, t_l28
    );

    // 3. Emit CSV and side-by-side Markdown comparison report
    let reports_dir = Path::new("../reports");
    std::fs::create_dir_all(reports_dir).expect("mkdir reports");

    let mut csv = File::create(reports_dir.join("rust_layer28_results.csv")).unwrap();
    writeln!(
        csv,
        "solver,suite,instance_id,family,target_n,n_vars,m_clauses,ground_truth,outcome,false_sat,false_unsat,termination_reason,outer_rounds,restarts_used,unsat_cert_steps,runtime_sec,total_ops,max_int_bits,max_float_exp,peak_memory_bytes"
    )
    .unwrap();
    for r in rows_l2
        .iter()
        .chain(rows_l25.iter())
        .chain(rows_l275.iter())
        .chain(rows_l28.iter())
    {
        writeln!(
            csv,
            "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{:.6},{},{},{},{}",
            r.solver_name,
            r.suite,
            r.inst.id,
            r.inst.family,
            r.target_n,
            r.inst.n_vars,
            r.inst.m_clauses(),
            r.inst.ground_truth,
            outcome_str(r.res.outcome),
            r.false_sat,
            r.false_unsat,
            r.res.termination_reason,
            r.res.outer_rounds,
            r.res.restarts_used,
            r.res.unsat_cert_steps,
            r.res.runtime_sec,
            r.res.ledger.total_ops(),
            r.res.ledger.max_int_bits,
            r.res.ledger.effective_max_float_exp(),
            r.res.ledger.peak_memory_bytes,
        )
        .unwrap();
    }

    let b2 = aggregate(&rows_l2);
    let b25 = aggregate(&rows_l25);
    let b275 = aggregate(&rows_l275);
    let b28 = aggregate(&rows_l28);

    let mut md = File::create(reports_dir.join("rust_layer28_comparison.md")).unwrap();
    writeln!(md, "# Layer 2 vs. Layer 2.5 vs. Layer 2.75 vs. Layer 2.8 Side-by-Side Falsification Report").unwrap();
    writeln!(md).unwrap();
    writeln!(md, "## 1. Parity Suite Validation (140 Instances, $n \\in \\{{15, 30, 60\\}}$)").unwrap();
    writeln!(md, "| Solver | `VERIFIED_SAT` (/101) | `VERIFIED_UNSAT` (/39) | `UNRESOLVED` | `FALSE_SAT` | `FALSE_UNSAT` | `OVERFLOW` | Runtime (s) |").unwrap();
    writeln!(md, "|---|---:|---:|---:|---:|---:|---:|---:|").unwrap();
    writeln!(md, "| **Layer 2 (`HybridGroebnerCascade`)** | {} | {} | {} | {} | {} | {} | {:.4} |", p_l2.0, p_l2.1, p_l2.2, p_l2.3, p_l2.4, p_l2.5, p_l2.6).unwrap();
    writeln!(md, "| **Layer 2.5 (`GadgetSPCascade`)** | {} | {} | {} | {} | {} | {} | {:.4} |", p_l25.0, p_l25.1, p_l25.2, p_l25.3, p_l25.4, p_l25.5, p_l25.6).unwrap();
    writeln!(md, "| **Layer 2.75 (`GadgetSP + CuttingPlanes`)** | {} | {} | {} | {} | {} | {} | {:.4} |", p_l275.0, p_l275.1, p_l275.2, p_l275.3, p_l275.4, p_l275.5, p_l275.6).unwrap();
    writeln!(md, "| **Layer 2.8 (`GadgetSP + CP + FLP + Nogoods`)** | {} | {} | {} | {} | {} | {} | {:.4} |", p_l28.0, p_l28.1, p_l28.2, p_l28.3, p_l28.4, p_l28.5, p_l28.6).unwrap();
    writeln!(md).unwrap();

    writeln!(md, "## 2. High-Scale Side-by-Side Comparison ($n \\in \\{{150, 300, 600\\}}$, 72 Instances)").unwrap();
    writeln!(md).unwrap();
    writeln!(md, "| Family | Target $n$ | L2.5 Solve (S/U/?) | L2.75 Solve (S/U/?) | L2.8 Solve (S/U/?) | L2.8 Avg Time (s) | L2.8 `max_int`/`exp` |").unwrap();
    writeln!(md, "|---|---:|---|---|---|---:|---|").unwrap();

    let families = [
        "F1_random_crit",
        "F2_planted_hard",
        "F3_tseitin_expander_sat",
        "F3_tseitin_expander_unsat",
        "F4_3sat_high_girth",
        "F5_pigeonhole",
    ];
    for fam in families {
        for &tn in &[150usize, 300usize, 600usize] {
            let k = (fam.to_string(), tn);
            let _a = &b2[&k];
            let b = &b25[&k];
            let c = &b275[&k];
            let d = &b28[&k];
            let r_b = 100.0 * ((b.vsat + b.vunsat) as f64) / (b.total as f64);
            let r_c = 100.0 * ((c.vsat + c.vunsat) as f64) / (c.total as f64);
            let r_d = 100.0 * ((d.vsat + d.vunsat) as f64) / (d.total as f64);
            writeln!(
                md,
                "| `{fam}` | {tn} | {r_b:.1}% ({}S/{}U/{}?) | {r_c:.1}% ({}S/{}U/{}?) | **{r_d:.1}%** ({}S/{}U/{}?) | {:.4} | {} / {} |",
                b.vsat, b.vunsat, b.unres,
                c.vsat, c.vunsat, c.unres,
                d.vsat, d.vunsat, d.unres,
                d.sum_time / (d.total as f64),
                d.max_int_bits, d.max_float_exp,
            )
            .unwrap();
        }
    }

    let summary_line = |label: &str, rows: &[Row], t: f64| -> String {
        let sat = rows.iter().filter(|r| r.res.outcome == SolveOutcome::VerifiedSat).count();
        let unsat = rows.iter().filter(|r| r.res.outcome == SolveOutcome::VerifiedUnsat).count();
        let unres = rows.iter().filter(|r| r.res.outcome == SolveOutcome::Unresolved).count();
        let ovf = rows.iter().filter(|r| r.res.outcome == SolveOutcome::Overflow).count();
        let fs = rows.iter().filter(|r| r.false_sat).count();
        let fu = rows.iter().filter(|r| r.false_unsat).count();
        format!(
            "- **{label} (72 high-scale):** `VERIFIED_SAT={sat}`, `VERIFIED_UNSAT={unsat}`, `UNRESOLVED={unres}`, `FALSE_SAT={fs}`, `FALSE_UNSAT={fu}`, `OVERFLOW={ovf}`, runtime `{t:.3}s`"
        )
    };
    writeln!(md).unwrap();
    writeln!(md, "{}", summary_line("Layer 2", &rows_l2, t_l2)).unwrap();
    writeln!(md, "{}", summary_line("Layer 2.5", &rows_l25, t_l25)).unwrap();
    writeln!(md, "{}", summary_line("Layer 2.75", &rows_l275, t_l275)).unwrap();
    writeln!(md, "{}", summary_line("Layer 2.8", &rows_l28, t_l28)).unwrap();
    println!("{}", summary_line("Layer 2.8", &rows_l28, t_l28));
}
