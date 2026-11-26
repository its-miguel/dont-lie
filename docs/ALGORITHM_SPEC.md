# PD-PFGC: Mathematical Specification, Complexity, and Bit-Width Bounds

## 1. Problem Definition

A **Monotone (Positive) 1-in-3 SAT** instance with $n$ Boolean variables $x \in \{0, 1\}^n$ and $m$ positive 3-literal clauses $C_1, \dots, C_m$, where $C_j = (a_j, b_j, c_j) \in \{0, \dots, n-1\}^3$, asks for an assignment $x \in \{0, 1\}^n$ such that:
$$x_{a_j} + x_{b_j} + x_{c_j} = 1 \qquad \forall j \in \{1, \dots, m\}.$$

Let $A \in \{0, 1, 2, 3\}^{m \times n}$ denote the clause-variable incidence matrix with $A_{ji} = |\{r \in \{1, 2, 3\} : C_{j,r} = i\}|$. The satisfiability condition is $Ax = \mathbf{1}_m$ with $x \in \{0, 1\}^n$.

### Fundamental Continuous LP Trap
Because every row of $A$ sums to $3$ ($A \mathbf{1}_n = 3 \mathbf{1}_m$), the interior fractional point
$$x^*_{\mathrm{LP}} = \frac{1}{3}\mathbf{1}_n \in [0, 1]^n$$
satisfies $A x^*_{\mathrm{LP}} = \mathbf{1}_m$ for **every** valid Monotone 1-in-3 SAT instance—even UNSAT instances. Therefore, the pure LP relaxation $\{x \in [0, 1]^n : Ax = \mathbf{1}_m\}$ is never infeasible, no purely linear Farkas UNSAT certificate can exist, and continuous relaxations without symmetry breaking and integrality enforcement risk collapsing to $x \approx \frac{1}{3}\mathbf{1}_n$.

To resolve this, define the variable degree vector $d := A^\top \mathbf{1}_m \in \mathbb{Z}_{\ge 0}^n$ ($\sum_{i=0}^{n-1} d_i = 3m$) and the **Global Conflict Matrix**:
$$K := A^\top A - \operatorname{diag}(d) \in \mathbb{Z}_{\ge 0}^{n \times n}.$$
For every $x \in \{0, 1\}^n$ (using $x_i^2 = x_i$),
$$x^\top K x = \|Ax\|_2^2 - \mathbf{1}_m^\top Ax = \sum_{j=1}^m (Ax)_j\big((Ax)_j - 1\big),$$
which vanishes if and only if $(Ax)_j \in \{0, 1\}$ for all clauses $j$ (and diagonal $K_{ii} = \sum_j A_{ji}(A_{ji}-1) > 0$ penalizes setting a repeated-literal variable to $1$).

---

## 2. State Space of PD-PFGC

At iteration $t \in \{0, 1, \dots, T_{\max}-1\}$, **Primal-Dual Polyrhythmic Fisher-Rao Geodesic Collapse (PD-PFGC)** maintains the state tuple
$$\mathcal{S}^{(t)} = \Big(\phi^{(t)},\; p^{(t)},\; x^{(t)},\; \lambda^{(t)},\; y_{\mathrm{cert}}^{(t)},\; s_{\mathrm{cert}}^{(t)}\Big)$$
where:
- $\phi^{(t)} \in (-\pi, \pi]^n \cong \mathbb{T}^n$: folded Fisher-Rao torus phase angles;
- $p^{(t)} \in \mathbb{R}^n$: geodesic momentum vector on $\mathbb{T}^n$;
- $x^{(t)} \in [0, 1]^n$: embedded continuous primal assignment $x_i^{(t)} = \sin^2(\phi_i^{(t)}/2)$;
- $\lambda^{(t)} \in [-B_\lambda, B_\lambda]^m$: primal-dual saddle multipliers for $Ax = \mathbf{1}_m$;
- $y_{\mathrm{cert}}^{(t)} \in [-B_y, B_y]^m$, $s_{\mathrm{cert}}^{(t)} \in [-B_{s,\mathrm{eff}}, B_{s,\mathrm{eff}}]^n$: dual spectral-certificate variables constrained to $M_{\mathrm{cert}}(s_{\mathrm{cert}}^{(t)}) - \epsilon_{\mathrm{chol}} I_n \succ 0$, where $B_{s,\mathrm{eff}} := \max(B_s, \max_i d_i + 2\epsilon_{\mathrm{chol}} + 1)$ prevents initial clamping below $d_i + 2\epsilon_{\mathrm{chol}}$ on high-degree instances.

---

## 3. Mapping the Four Structural Primitives to Mathematical Operators

### Primitive 1: Global Unsat-Gate Collapse
1. **Adaptive Global Clause-Gate Weights:** From the clause residual $r^{(t)} = A x^{(t)} - \mathbf{1}_m \in [-1, 2]^m$, define
   $$w_j^{(t)} := 1 + \kappa_w \big(r_j^{(t)}\big)^2 \in [1, 1 + 4\kappa_w], \qquad j = 1, \dots, m.$$
2. **Global Gate Potential & Operator Gradient:**
   $$\Phi_{\mathrm{gate}}(x; w) := \frac{1}{2}(Ax - \mathbf{1}_m)^\top \operatorname{diag}(w)(Ax - \mathbf{1}_m) + \frac{\rho}{2}\|Ax - \mathbf{1}_m\|_2^2 + \frac{\alpha}{2} x^\top K x,$$
   $$\nabla_x \Phi_{\mathrm{gate}}(x; w) = A^\top\big((w + \rho\mathbf{1}_m) \odot (Ax - \mathbf{1}_m)\big) + \alpha K x.$$
3. **Global Gram-Resolvent Collapse Operator:** Precompute once at $t = 0$ ($\eta_0 > 0$) the strictly symmetric positive definite (SPD) normal operator and its Cholesky factorization:
   $$M_0 := I_n + \eta_0 A^\top A = L_0 L_0^\top \succ 0, \qquad \lambda_{\min}(M_0) \ge 1, \quad \lambda_{\max}(M_0) \le 1 + 9\eta_0 m.$$
   Applying $M_0^{-1} = L_0^{-\top} L_0^{-1}$ couples all $m$ clause constraints simultaneously across variables.

### Primitive 2: Continuous Manifold Folding & Geodesic Flow
Embed $(0, 1)^n$ endowed with the Fisher-Rao Riemannian metric $g_{ij}(x) = \frac{\delta_{ij}}{x_i(1-x_i)}$ onto the flat torus $\mathbb{T}^n = (-\pi, \pi]^n$ via the isometric coordinate folding map:
$$x_i(\phi_i) := \sin^2\!\left(\frac{\phi_i}{2}\right) = \frac{1 - \cos\phi_i}{2}, \qquad \sigma_i(\phi_i) := 1 - 2 x_i(\phi_i) = \cos\phi_i \in [-1, 1].$$
Because $dx_i = \frac{1}{2}\sin\phi_i\, d\phi_i$ and $x_i(1 - x_i) = \frac{1}{4}\sin^2\phi_i$, the metric pulls back identically to the Euclidean metric on $\mathbb{T}^n$:
$$ds_{\mathrm{FR}}^2 = \sum_{i=1}^n \frac{dx_i^2}{x_i(1 - x_i)} = \sum_{i=1}^n d\phi_i^2.$$
Thus $\{0, 1\}^n$ folds onto the antipodal lattice $\{0, \pi\}^n \subset \mathbb{T}^n$, and Riemannian natural gradient descent on $([0,1]^n, g_{\mathrm{FR}})$ becomes damped inertial geodesic flow on $\mathbb{T}^n$ with Jacobian pullback $\frac{\partial x_i}{\partial \phi_i} = \frac{1}{2}\sin\phi_i$.

### Primitive 3: Polyrhythmic Phase Interference & Spectral Mode Filtering
1. **Exact Boolean-Fourier (Walsh-Hadamard) Clause Harmonic:** In spin coordinates $\sigma_i = \cos\phi_i$, the multilinear unsatisfied clause polynomial $U_j(\sigma) = 1 - \mathbb{I}[x_{a_j}+x_{b_j}+x_{c_j}=1]$ is
   $$U_j(\sigma) = \frac{5}{8} - \frac{1}{8}(\sigma_{a_j}+\sigma_{b_j}+\sigma_{c_j}) + \frac{1}{8}(\sigma_{a_j}\sigma_{b_j}+\sigma_{b_j}\sigma_{c_j}+\sigma_{c_j}\sigma_{a_j}) + \frac{3}{8}\sigma_{a_j}\sigma_{b_j}\sigma_{c_j}.$$
   For all $\sigma \in [-1, 1]^n$, $U_j(\sigma) \ge 0$, and $U_j(\sigma) = 0$ iff $(x_{a_j}, x_{b_j}, x_{c_j}) \in \{0,1\}^3$ satisfies $C_j$. With weighted potential $\Phi_{\mathrm{WF}}(\phi; w) = \sum_{j=1}^m w_j U_j(\cos\phi)$, the exact $\phi$-gradient is
   $$\big[\nabla_\phi \Phi_{\mathrm{WF}}(\phi; w)\big]_i = -\sin(\phi_i) \sum_{j=1}^m w_j \sum_{\substack{r \in \{1, 2, 3\}\\ C_{j,r} = i}} \frac{-1 + \sigma_{r'} + \sigma_{r''} + 3\sigma_{r'}\sigma_{r''}}{8},$$
   where $(r', r'')$ are the remaining two literal slots of clause $j$.
2. **Coprime Dual-Frequency Clause-Beat Wave:** With $\omega_1 = \pi/3$ and $\omega_2 = \pi/2$,
   $$\Phi_{\mathrm{beat}}(\phi) := \sum_{j=1}^m \left(\frac{1 - \cos(\omega_1 r_j)}{\omega_1^2} + \frac{1 - \cos(\omega_2 r_j)}{\omega_2^2}\right), \qquad \nabla_x \Phi_{\mathrm{beat}} = A^\top\!\left(\frac{\sin(\omega_1 r)}{\omega_1} + \frac{\sin(\omega_2 r)}{\omega_2}\right).$$
   On $r_j \in [-1, 2]$, $\omega_1 r_j \in [-\pi/3, 2\pi/3]$ and $\omega_2 r_j \in [-\pi/2, \pi]$ remain strictly in the primary single-well basin around $r_j = 0$.
3. **Boolean Pinning Wave & Anti-Synchronization Spectral Filter:**
   $$\Phi_{\mathrm{pin}}(\phi) := \frac{\beta^{(t)}}{2} \sum_{i=1}^n \sin^2(\phi_i), \qquad \big[\nabla_\phi \Phi_{\mathrm{pin}}(\phi)\big]_i = \beta^{(t)} \sin(\phi_i)\cos(\phi_i),$$
   with annealing schedule $\beta^{(t)} = \beta_{\min} + (\beta_{\max} - \beta_{\min}) \min(1, t / T_{\mathrm{anneal}})$.
   Define $(D_K)_{ii} := \max(1, \sum_{k=0}^{n-1} K_{ik}) = \max(1, 2 d_i)$ and $K_{\mathrm{norm}} := D_K^{-1/2} K D_K^{-1/2}$. By Gershgorin's circle theorem on $D_K^{-1}K$ (since $K_{ik} \ge 0$), $\lambda(K_{\mathrm{norm}}) \subseteq [-1, 1]$. For $\eta_{\mathrm{spec}} \in (0, 1/2]$, define
   $$\mathcal{F}_{\mathrm{spec}} := I_n - \eta_{\mathrm{spec}} K_{\mathrm{norm}}, \qquad \lambda(\mathcal{F}_{\mathrm{spec}}) \subseteq \left[\frac{1}{2}, \frac{3}{2}\right].$$
   The symmetric composite preconditioner $P_{\mathrm{comb}} := \mathcal{F}_{\mathrm{spec}} M_0^{-1} \mathcal{F}_{\mathrm{spec}} \succ 0$ damps in-phase conflict eigenvectors ($+1$) and amplifies anti-phase independent-set eigenvectors ($-1$) while preserving strict positive definiteness.
4. **Polyrhythmic Symmetry-Breaking Kick:** On stagnation (if $\min_{\tau \le t} \|r^{(\tau)}\|_2$ has not improved by at least $\epsilon_{\mathrm{imp}}$ over $W_{\mathrm{stall}}$ consecutive steps), apply
   $$\xi_i^{(t)} = \epsilon_{\mathrm{kick}} \Big[\mathcal{F}_{\mathrm{spec}}\Big(\cos\!\left(\tfrac{2\pi i}{3} + t\omega_1\right) - \cos\!\left(\tfrac{2\pi i}{5} + t\omega_2\right)\Big)\Big]_i$$
   and reset the stall counter; otherwise $\xi^{(t)} = \mathbf{0}_n$.

### Primitive 4: Primal-Dual Symmetry & Spectral Dual Certificate $\mathcal{D}_{\mathrm{spec}}$
1. **Primal-Dual Saddle System:**
   $$\mathcal{L}_{\mathrm{PD}}(\phi, \lambda) = \Phi_{\mathrm{gate}}(x(\phi); w) + \gamma_{\mathrm{WF}} \Phi_{\mathrm{WF}}(\phi; w) + \gamma_{\mathrm{beat}} \Phi_{\mathrm{beat}}(\phi) + \Phi_{\mathrm{pin}}(\phi) + \lambda^\top (A x(\phi) - \mathbf{1}_m).$$
2. **Quadratic Spectral Dual Certificate $\mathcal{D}_{\mathrm{spec}}(y, s)$:**
   For any $y \in \mathbb{R}^m$ and $s \in \mathbb{R}^n$ satisfying $M_{\mathrm{cert}}(s) := K + A^\top A + \operatorname{diag}(s) \succ 0$, every Boolean solution $x \in \{0, 1\}^n$ with $Ax = \mathbf{1}_m$ satisfies $x^\top K x = 0$, $\|Ax - \mathbf{1}_m\|_2^2 = 0$, $y^\top(Ax - \mathbf{1}_m) = 0$, and $s^\top(x^{\odot 2} - x) = 0$. Summing gives
   $$0 = x^\top M_{\mathrm{cert}}(s) x + b(y, s)^\top x + (m - y^\top \mathbf{1}_m) \ge \mathcal{D}_{\mathrm{spec}}(y, s),$$
   where $b(y, s) := A^\top y - 2 A^\top \mathbf{1}_m - s$, $x_{\mathrm{dual}}(y, s) := -\frac{1}{2} M_{\mathrm{cert}}(s)^{-1} b(y, s)$, and
   $$\mathcal{D}_{\mathrm{spec}}(y, s) := m - y^\top \mathbf{1}_m - x_{\mathrm{dual}}^\top M_{\mathrm{cert}}(s) x_{\mathrm{dual}}.$$
   - **Soundness:** If Cholesky factorization confirms $M_{\mathrm{cert}}(s) - \epsilon_{\mathrm{chol}} I_n \succ 0$ and $\mathcal{D}_{\mathrm{spec}}(y, s) > \epsilon_{\mathrm{cert}}$, then no $x \in \{0, 1\}^n$ can satisfy $Ax = \mathbf{1}_m$, so the instance is **provably UNSAT**.
   - **Joint Concavity & Ascent Gradients:** $\mathcal{D}_{\mathrm{spec}}$ is jointly concave on $\mathbb{R}^m \times \{s : M_{\mathrm{cert}}(s) \succ 0\}$ with exact gradients
     $$\nabla_y \mathcal{D}_{\mathrm{spec}} = A x_{\mathrm{dual}} - \mathbf{1}_m, \qquad \nabla_s \mathcal{D}_{\mathrm{spec}} = x_{\mathrm{dual}}^{\odot 2} - x_{\mathrm{dual}}.$$
   - **Canonical Verification Example ($K_4^3$):** For the 4-variable complete 3-uniform hypergraph ($n=4, m=4$), $M_{\mathrm{cert}}(\mathbf{1}_4) = 4 J_4$. At $y = \mathbf{0}_4, s = (1+\epsilon)\mathbf{1}_4$, $\mathcal{D}_{\mathrm{spec}} = 4 - \frac{(7+\epsilon)^2}{16+\epsilon} \to \frac{15}{16} > 0$. At optimal $y^* = -\frac{11}{9}\mathbf{1}_4, s \to \mathbf{1}_4^+$, $\mathcal{D}_{\mathrm{spec}} \to \frac{16}{9} > 0$ (whereas omitting $+A^\top A$ in $M_{\mathrm{cert}}$ gives $8/9 > 0$).

---

## 4. Initialization & Iteration Equations

### Initialization ($t = 0$)
- Precompute sparse incidence structures for $A$, degrees $d = A^\top \mathbf{1}_m$, $D_K^{-1/2}$, and Cholesky factor $L_0 L_0^\top = M_0 = I_n + \eta_0 A^\top A$.
- Deterministic symmetry-breaking around $x = \frac{1}{3}\mathbf{1}_n$ ($\phi_{\mathrm{base}} = \arccos(1/3) = 2\arcsin(\sqrt{1/3}) \approx 1.2309594$):
  $$\phi_i^{(0)} = \phi_{\mathrm{base}} + \delta_0 \sin\!\left(\frac{2\pi(i+1)}{n+1}\right), \qquad p^{(0)} = \mathbf{0}_n, \qquad \lambda^{(0)} = \mathbf{0}_m.$$
- Initialize strictly positive-definite dual certificate state:
  $$y_{\mathrm{cert}}^{(0)} = \mathbf{0}_m, \qquad s_{\mathrm{cert}}^{(0)} = d + 2\epsilon_{\mathrm{chol}}\mathbf{1}_n \quad \big(\implies M_{\mathrm{cert}}(s_{\mathrm{cert}}^{(0)}) - \epsilon_{\mathrm{chol}} I_n = 2 A^\top A + \epsilon_{\mathrm{chol}} I_n \succ 0\big).$$

### Iteration $t = 0, \dots, T_{\max}-1$
1. **Manifold & Residual:**
   $$x_i^{(t)} = \frac{1 - \cos\phi_i^{(t)}}{2}, \quad \sigma_i^{(t)} = \cos\phi_i^{(t)}, \quad r^{(t)} = A x^{(t)} - \mathbf{1}_m, \quad w_j^{(t)} = 1 + \kappa_w (r_j^{(t)})^2.$$
2. **Primal-Dual Gradient & Pullback:**
   $$g_x^{(t)} = A^\top\!\left((w^{(t)} + \rho\mathbf{1}_m) \odot r^{(t)} + \lambda^{(t)} + \gamma_{\mathrm{beat}}\!\left(\frac{\sin(\omega_1 r^{(t)})}{\omega_1} + \frac{\sin(\omega_2 r^{(t)})}{\omega_2}\right)\right) + \alpha K x^{(t)},$$
   $$g_\phi^{(t)} = \frac{1}{2}\sin(\phi^{(t)}) \odot g_x^{(t)} + \gamma_{\mathrm{WF}}\nabla_\phi \Phi_{\mathrm{WF}}(\phi^{(t)}; w^{(t)}) + \beta^{(t)} \sin(\phi^{(t)}) \odot \cos(\phi^{(t)}).$$
3. **Preconditioning & Spectral Filtering:**
   $$\tilde{g}_\phi^{(t)} = \mathcal{F}_{\mathrm{spec}}\!\left(L_0^{-\top} L_0^{-1} \big(\mathcal{F}_{\mathrm{spec}} g_\phi^{(t)}\big)\right).$$
4. **Momentum, Wrapping & Over-Relaxed PDHG Multiplier Update:**
   $$p^{(t+1)} = \mu_{\mathrm{damp}} p^{(t)} - \tau_{\mathrm{step}} \tilde{g}_\phi^{(t)} + \xi^{(t)}, \qquad \phi^{(t+1)} = \big((\phi^{(t)} + p^{(t+1)} + \pi) \bmod 2\pi\big) - \pi,$$
   $$\bar{x}^{(t)} = x^{(t)} + \vartheta(x^{(t)} - x^{(t-1)}), \qquad \lambda^{(t+1)} = \Pi_{[-B_\lambda, B_\lambda]^m}\!\Big((1 - \eta_d \delta_d)\lambda^{(t)} + \eta_d(A\bar{x}^{(t)} - \mathbf{1}_m)\Big).$$
5. **Dual Spectral Certificate Ascent (Per-Step or Amortized every $B_{\mathrm{cert}}$ Steps):**
   Using cached (or refreshed) Cholesky factors of $M_{\mathrm{cert}}(s_{\mathrm{cert}}^{(t)})$, solve $M_{\mathrm{cert}} x_{\mathrm{dual}}^{(t)} = -\frac{1}{2} b(y_{\mathrm{cert}}^{(t)}, s_{\mathrm{cert}}^{(t)})$, evaluate $\mathcal{D}_{\mathrm{spec}}^{(t)}$, update
   $$y_{\mathrm{cert}}^{(t+1)} = \Pi_{[-B_y, B_y]^m}\!\big(y_{\mathrm{cert}}^{(t)} + \alpha_y (A x_{\mathrm{dual}}^{(t)} - \mathbf{1}_m)\big),$$
   and when $t \equiv 0 \pmod{B_{\mathrm{cert}}}$ (with $B_{\mathrm{cert}} = 1$ for per-step mode or $B_{\mathrm{cert}} = n$ for amortized mode), update $s_{\mathrm{cand}} = \Pi_{[-B_{s,\mathrm{eff}}, B_{s,\mathrm{eff}}]^n}(s_{\mathrm{cert}}^{(t)} + \alpha_s((x_{\mathrm{dual}}^{(t)})^{\odot 2} - x_{\mathrm{dual}}^{(t)}))$ (clamping degree-0 variables $s_i \ge 2\epsilon_{\mathrm{chol}}$) with up to $k_{\mathrm{bt}}$ global halving steps until Cholesky succeeds on $M_{\mathrm{cert}}(s_{\mathrm{cand}}) - \epsilon_{\mathrm{chol}} I_n \succ 0$; if global backtracking is blocked by boundary coordinates, compute exact single-coordinate PD margins $\mu_i = 1 / ((M_{\mathrm{cert}}(s_{\mathrm{cert}}^{(t)}) - \epsilon_{\mathrm{chol}} I_n)^{-1})_{ii}$ in $\frac{1}{6}n^3$ ops and accept decreasing coordinates in ascending order of $\delta_i / \mu_i$ under the trace-PD budget $\sum \delta_i / \mu_i \le 0.85 < 1$ (keeping total update cost $O(n^3 + m)$, $O(n^2 + m)$ amortized).
6. **Discretization & Termination:**
   - Construct $\hat{x}_{\mathrm{thr}}^{(t)} = \mathbb{I}[x^{(t)} \ge 0.5]$ and conflict-aware greedy sweep $\hat{x}_{\mathrm{greedy}}^{(t)}$ (variables sorted by descending $x_i^{(t)}$, setting $\hat{x}_i = 1$ iff $A_{ji} \le 1$ and no clause $j$ containing $i$ already has a true literal).
   - Check both candidates using the isolated deterministic verifier (`verifier.py`). If either passes, return `SAT`.
   - If $M_{\mathrm{cert}}(s_{\mathrm{cert}}^{(t)}) - \epsilon_{\mathrm{chol}} I_n \succ 0$ is verified by Cholesky and
     $$\mathcal{D}_{\mathrm{spec}}^{(t)} > \epsilon_{\mathrm{cert}} := 10^{-6} + n^2 \epsilon_{\mathrm{mach}} \frac{18m + B_{s,\mathrm{eff}}}{\epsilon_{\mathrm{chol}}} \|x_{\mathrm{dual}}^{(t)}\|_2^2,$$
     return `UNSAT_CERTIFIED`.
   - If $t = T_{\max} - 1$ or time/bit-width limits are reached, return `UNRESOLVED` (or `OVERFLOW` if NaN/Inf/bit-width guardrail triggered).

---

## 5. Exact Per-Iteration Operation Count

Because each clause has 3 literals, $\mathrm{nnz}(A) \le 3m$. Matrix-vector products $Ax$, $A^\top v$, and $Kx = A^\top(Ax) - d \odot x$ use sparse 3-literal incidence lists in $O(m + n)$ operations.

| Stage | Arithmetic / Elementary Operations | Asymptotic Cost |
|---|---|---|
| **Setup ($t=0$, once)** | Build $A, d, K, D_K^{-1/2}$: $9m + 6n$; Form $M_0$ & Cholesky $L_0 L_0^\top$: $\frac{1}{3}n^3 + O(n^2 + m)$ | $O(n^3 + m)$ |
| **1. Manifold & residual** | $n$ $(\sin,\cos)$ + $3n$ arith; $r = Ax - \mathbf{1}_m$: $4m$; $w$: $3m$ | $7m + 3n$ (+ $n$ trig) |
| **2. Gate & $x$-gradient** | Beat wave: $2m$ $\sin$ + $5m$; $A^\top(\dots)$: $6m$; $Kx = A^\top(Ax) - d\odot x$: $4m + 2n$ | $15m + 2n$ (+ $2m$ trig) |
| **3. Fourier & pullback** | $\nabla_\phi \Phi_{\mathrm{WF}}$: $27m + n$; pinning & pullback: $6n$ | $27m + 7n$ |
| **4. Precondition & filter** | Two sparse $\mathcal{F}_{\mathrm{spec}}$ matvecs: $12m + 10n$; $L_0^{-\top} L_0^{-1}$ solve: $2n^2$ | $2n^2 + 12m + 10n$ |
| **5. Momentum, wrap, $\lambda$** | Momentum & $\bmod 2\pi$ wrap: $10n$ (+ $4n$ trig on kick); $\bar{x}, \lambda^{(t+1)}$: $2n + 7m$ | $7m + 12n$ |
| **6. Dual certificate branch** | $(1 + k_{\mathrm{bt}})$ Cholesky checks: $\le \frac{1 + k_{\mathrm{bt}}}{3}n^3 + O(n^2)$; solve & update: $2n^2 + 12m + 8n$ | $\frac{1+k_{\mathrm{bt}}}{3}n^3 + O(n^2 + m)$ |
| **7. Rounding & verifier** | Threshold + greedy sort + deterministic verifier: $O(n\log n) + 9m + 2n$ | $O(n\log n + m)$ |

- **Per-step dual Cholesky ($B_{\mathrm{cert}} = 1$):**
  $$\frac{1 + k_{\mathrm{bt}}}{3} n^3 + 4n^2 + O(n \log n + m) = O(n^3 + m).$$
- **Amortized dual Cholesky ($B_{\mathrm{cert}} = n$, updating only $y_{\mathrm{cert}}$ via cached $L_{\mathrm{cert}}$ between $s_{\mathrm{cert}}$ updates):**
  $$4n^2 + O(n \log n + m) = O(n^2 + m).$$

---

## 6. Explicit Worst-Case Bit-Width & Conditioning Bounds

1. **Exact Integer Bit-Widths (Static & Verification Arithmetic):**
   - Incidence entries $A_{ji} \in \{0, 1, 2, 3\}$: **2 bits**.
   - Variable degrees $d_i \in [0, 3m]$: $\lceil \log_2(3m + 1) \rceil$ bits.
   - Entries of $A^\top A$ and $K$ in $[0, 9m]$: $\lceil \log_2(9m + 1) \rceil$ bits.
   - Verifier clause sums $(A\hat{x})_j \in \{0, 1, 2, 3\}$: **2 bits**.
2. **Exact Rational ($\mathbb{Q}$) vs. Clamped Fixed-Point ($2^{-q}\mathbb{Z}$):**
   - **One-shot exact solve ($M_0^{-1}$):** By Hadamard's inequality, $\det(M_0) \le (\sqrt{n}(1 + 9\eta_0 m))^n$, bounding rational solution bit-width by $O(n \log(nm))$ bits.
   - **Unrounded iterative rational execution:** Because $U_j(\sigma)$ and $w_j r_j$ are degree-3 polynomials, iterating without precision truncation yields worst-case rational numerator/denominator bit-width growth of **$O(3^t)$** across $t$ steps.
   - **Clamped fixed-point ($q$ fractional bits):** With box clamping $|\phi_i| \le \pi$, $|\lambda_j| \le B_\lambda$, $|y_j| \le B_y$, $|s_i| \le B_{s,\mathrm{eff}}$, intermediate magnitudes are bounded by $O(m(1 + \kappa_w + B_\lambda + B_y + B_{s,\mathrm{eff}}))$, requiring
     $$b_{\mathrm{fixed}} \le q + \left\lceil \log_2\!\big(1 + C m (1 + \kappa_w + B_\lambda + B_y + B_{s,\mathrm{eff}})\big) \right\rceil = q + O(\log m) \text{ bits}.$$
3. **IEEE-754 Floating-Point (`float64`) Conditioning & Dynamic Range:**
   - Physical storage is 64 bits ($\epsilon_{\mathrm{mach}} = 2^{-53}$).
   - $\kappa_2(M_0) \le 1 + 9\eta_0 m = O(m)$, losing at most $\log_2(1 + 9\eta_0 m) = O(\log m)$ bits.
   - Enforcing $M_{\mathrm{cert}}(s) - \epsilon_{\mathrm{chol}} I_n \succ 0$ and $\|s\|_\infty \le B_{s,\mathrm{eff}}$ bounds $\lambda_{\min}(M_{\mathrm{cert}}) > \epsilon_{\mathrm{chol}}$ and $\lambda_{\max}(M_{\mathrm{cert}}) \le 18m + B_{s,\mathrm{eff}}$, so
     $$\kappa_2(M_{\mathrm{cert}}) \le \frac{18m + B_{s,\mathrm{eff}}}{\epsilon_{\mathrm{chol}}}, \qquad \text{precision loss} \le \log_2\!\left(\frac{18m + B_{s,\mathrm{eff}}}{\epsilon_{\mathrm{chol}}}\right) \text{ bits}.$$
   - Clamping ($|\phi_i| \le \pi$, $|\lambda_j| \le B_\lambda$, $|y_j| \le B_y$, $|s_i| \le B_{s,\mathrm{eff}}$) bounds the **maximum** binary exponent $e_{\max} = O(\log m)$ (`max_float_exp`), condition-number precision loss ($\le \log_2((18m + B_{s,\mathrm{eff}})/\epsilon_{\mathrm{chol}})$ bits), and **quantized fixed-point** width ($q + O(\log m)$ bits on $2^{-q}\mathbb{Z}$). In **unquantized** IEEE-754 `float64`, however, the active dynamic-range span $(e_{\max} - e_{\min}) + 53$ (`max_dynamic_range_bits`) is **not** bounded by $53 + O(\log m)$: because damped momentum ($p^{(t+1)} = \mu_{\mathrm{damp}} p^{(t)} - \dots$), decaying residuals, and $x_i = (1 - \cos\phi_i)/2 \approx \phi_i^2/4$ near $\phi_i \to 0$ decay nonzero magnitudes toward zero, $e_{\min}$ grows downward toward negative exponents (potentially $O(t)$ down to $-1022$/$-1074$) unless values are quantized/floored at $2^{-q}$. Meanwhile, removing box bounds ($B_\lambda, B_y, B_s \to \infty$) causes $O(t)$ upper-exponent drift, removing $\epsilon_{\mathrm{chol}} > 0$ allows $\kappa_2(M_{\mathrm{cert}}) \to \infty$ near PSD boundaries, and unrounded rational iteration triggers $O(3^t)$ bit-width explosion.

---

## 7. Theoretical Falsification Hypotheses

1. **Expected Success Regimes:**
   - Sparse / underconstrained random instances ($m/n \lesssim 0.55$) and degree-balanced planted SAT instances away from the glassy boundary should collapse rapidly to verified SAT assignments.
   - Rank-1 quadratic-infeasible UNSAT cores (such as $K_4^3$ and locally dense odd-clique contradictions) should be deterministically certified via $\mathcal{D}_{\mathrm{spec}} > \epsilon_{\mathrm{cert}}$.
2. **Expected Failure / Breakage Regimes (Falsification Targets):**
   - **Degree-2 Feasible UNSAT Integrality Gap (Tseitin XOR UNSAT, Schaefer 3-SAT UNSAT, overconstrained sparse UNSAT):** Any UNSAT instance admitting a valid degree-2 (Shor-1) pseudo-expectation satisfies $\sup \mathcal{D}_{\mathrm{spec}} \le 0$ by weak duality. PD-PFGC cannot certify UNSAT on these instances and must exit as `UNRESOLVED`.
   - **Critical-Threshold Phase Frustration ($\alpha_c \approx 0.626$ and finite-size $\alpha_{50\%}(n)$) & Coupled Gadget Traps:** Near the satisfiability transition and on 3-SAT/Tseitin SAT reductions, metastable local minima and frustrated phase-locking can trap trajectories with near-zero primal residual or near $x \approx \frac{1}{3}\mathbf{1}$, causing super-polynomial iteration scaling or budget exhaustion as $n$ increases from $15 \to 30 \to 60$.
   - **Spectral Symmetry Traps:** On regular or vertex-transitive hypergraphs, degenerate eigenspaces of $K$ can funnel trajectories back toward balanced fractional saddles around $x = \frac{1}{3}\mathbf{1}$.
