# Gram matrices at the zeta zeros, Nyman–Beurling–Báez-Duarte lower bounds and Weil positivity on windows: context for λ_N ≥ c/N

Scope. Background for the RH-conditional corollary: Q_N(x) = Σ_{m,n≤N} x_m x_n √(mn) K(m/n), with K(r) = Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)), equals Σ_ρ |Σ_n x_n n^ρ|²/(1/4+γ²) under RH, and λ_min(Q_N) ≥ 1/(200 e^24 N), with numerics λ_N ≈ 0.048 log N/N. A source tag means I read that source in this session: "full text" means the arXiv PDF, "abstract" means the abstract only, and "as restated by X" means I did not read the primary source and rely on X's statement of it. Anything without a source is under Inferences or Gaps. Arithmetic marked "(computed here)" is mine.

## Q1. Nyman–Beurling–Báez-Duarte: lower bounds for d_N, Báez-Duarte's conjecture, Bettin–Conrey–Farmer, and how the lower bounds are proved

### Takeaway
The known lower bound is lim inf d_N² log N ≥ Σ_ρ m_ρ²/|ρ|² (Burnol 2002). It improves the earlier bound of Báez-Duarte, Balazard, Landreau and Saias (BBLS 2000), which had Σ 1/|ρ|² over distinct zeros. Under RH with simple zeros the constant is 2+γ−log 4π ≈ 0.0462. Bettin–Conrey–Farmer show that the mollified polynomial V_N reaches this constant, assuming RH and Σ_{|γ|≤T} 1/|ζ'(ρ)|² ≪ T^{3/2−δ}. The lower bounds come from an interpolation argument at a fixed finite set of zeros: vectors attached to the zeros are orthogonal to the approximating space and become asymptotically orthogonal to each other as N → ∞. It is not a sampling inequality that holds uniformly in N over all zeros up to T ≫ N. It gives only a lim inf, with no explicit dependence on N.

### Cited Findings
- **Setup (Báez-Duarte's natural form).** RH holds iff d_N² → 0, where d_N² = inf_{A_N} (1/2π)∫_ℝ |1 − ζA_N(1/2+it)|² dt/(1/4+t²) and A_N(s) = Σ_{n≤N} a_n n^{−s} — [Bettin–Conrey–Farmer, arXiv:1211.5191, full text](https://arxiv.org/abs/1211.5191).
  - Equivalent form: d_n² = inf_b ∫_0^∞ |1_{(0,1)} − Σ_{k≤n} b_k {1/(kx)}|² dx. As a ratio of Gram determinants, d_n² = det G(ρ_1,…,ρ_n, 1_{(0,1)}) / det G(ρ_1,…,ρ_n) with ρ_k(x) = {1/(kx)} — [Dimitrov–Oliveira, arXiv:1608.07887, full text](https://arxiv.org/abs/1608.07887).
- **Báez-Duarte's strengthening.** RH is equivalent to χ_{(0,1)} lying in the closure of the span of ρ_a(x) = ρ(1/(ax)) over integers a ∈ ℕ. Under RH, for some c > 0, the distance from χ to −Σ_{a≤n} μ(a) e^{−c log a / log log n} ρ_a is of order (log log n)^{−1/3} — [Báez-Duarte, arXiv:math/0202141](https://arxiv.org/abs/math/0202141); [arXiv:math/0205003, abstract](https://arxiv.org/abs/math/0205003).
  - Published as Rend. Mat. Acc. Lincei (9) 14 (2003), 5–11 — [as listed in Balazard–de Roton's references](https://arxiv.org/abs/0812.1689).
- **Upper bounds under RH.** Báez-Duarte gave d_N² ≪ (log log N)^{−2/3}, with the proof credited to Balazard. Balazard–de Roton prove d_N² ≪_δ (log log N)^{5/2+δ}(log N)^{−1/2} for N ≥ 3 — [Balazard–de Roton, arXiv:0812.1689, full text; Int. J. Number Theory 6 (2010) 883–903](https://arxiv.org/abs/0812.1689) ([DOI](https://doi.org/10.1142/S1793042110003307)).
- **BBLS 2000 lower bound (I did not read BBLS itself).** BBLS, "Notes sur la fonction ζ de Riemann, 3", Adv. Math. 149 (2000) 130–144 — [DOI](https://doi.org/10.1006/aima.1999.1861).
  - **Burnol's restatement (Thm 1.2).** Let B_λ be the finite combinations of t ↦ ρ(θ/t) with λ ≤ θ ≤ 1 (continuous dilations), and D(λ) = inf_{f∈B_λ} ‖χ − f‖. Then lim inf_{λ→0} D(λ)√(log(1/λ)) ≥ √(Σ_ρ 1/|ρ|²). Each zero is counted once, whatever its multiplicity. If RH fails the statement is "true but trivial", since the left side is +∞ — [Burnol, arXiv:math/0103058, full text](https://arxiv.org/abs/math/0103058).
  - **BCF's restatement.** In the natural form: BBLS showed "(unconditionally)" that lim inf d_N² log N ≥ Σ_{Re ρ=1/2} 1/|ρ|² over distinct zeros on the critical line, citing BBLS 2000 and BBLS 2005 (Ramanujan J. 9 (2005) 215–240) — [BCF](https://arxiv.org/abs/1211.5191); [BBLS 2005 DOI](https://doi.org/10.1007/s11139-005-0834-4).
- **Burnol 2002 (Adv. Math. 170, 56–70), Thm 1.3.** lim inf_{λ→0} D(λ)√(log(1/λ)) ≥ √(Σ_ρ m_ρ²/|ρ|²): "the zeros are counted according to the square of their multiplicities" — [Burnol, full text](https://arxiv.org/abs/math/0103058) ([DOI](https://doi.org/10.1006/aima.2001.2066)).
  - Balazard–de Roton quote it as d_N² ≥ (C+o(1))/log N with C = Σ_ρ m(ρ)²/|ρ|² — [BdR](https://arxiv.org/abs/0812.1689).
  - De Roton extended the lower bound to the Selberg class — [as stated by Dimitrov–Oliveira](https://arxiv.org/abs/1608.07887); generalised criterion in [de Roton, TAMS 359 (2007) 6111–6126](https://doi.org/10.1090/S0002-9947-07-04261-4).
- **Value of the constant.** Under RH, Σ_ρ m(ρ)/|ρ|² = 2 + γ − log(4π) (BdR cite Davenport ch. 12). Hence d_N² ≥ (2+γ−log 4π + o(1))/log N — [BdR, eq. (3)](https://arxiv.org/abs/0812.1689); [BCF](https://arxiv.org/abs/1211.5191). Numerically 2 + γ − log 4π = 0.046191… (computed here).
- **The conjecture.**
  - BdR: "les auteurs de [3] [= BBLS 2000] conjecturent l'égalité dans (3)", and this would imply both RH and simplicity of the zeros — [BdR](https://arxiv.org/abs/0812.1689).
  - BCF: "This lower bound is believed to be optimal and one expects d_N² ∼ (1/log N) Σ_{Re ρ=1/2} m(ρ)²/|ρ|²". With simple zeros this reads d_N² ∼ (2+γ−log 4π)/log N — [BCF](https://arxiv.org/abs/1211.5191).
- **Bettin–Conrey–Farmer, Thm 1.** Assume RH and Σ_{|Im ρ|≤T} 1/|ζ'(ρ)|² ≪ T^{3/2−δ} for some δ > 0. With V_N(s) = Σ_{n≤N}(1 − log n/log N) μ(n) n^{−s}, (1/2π)∫|1 − ζV_N(1/2+it)|² dt/(1/4+t²) ∼ (2+γ−log 4π)/log N — [BCF, full text](https://arxiv.org/abs/1211.5191).
  - The hypothesis implicitly assumes simple zeros. Gonek's conjecture, recovered by Hughes–Keating–O'Connell, predicts Σ_{|ρ|≤T} 1/|ζ'(ρ)|² ∼ (6/π³)T.
  - BCF say the result contrasts with Landreau–Richard's graphs, which "at first sight suggest that V_N is not optimal" ([Landreau–Richard, Exp. Math. 11 (2002) 349–360](https://doi.org/10.1080/10586458.2002.10504480), not read).
  - Polynomial analogue (BCF Thm 2): if P has simple zeros on or outside the unit circle, 1/P = Σ a_n zⁿ and W_N = Σ_{n≤N}(1 − n/N) a_n zⁿ, then (1/2π)∫|1 − PW_N|² dθ ∼ (1/N) Σ_{|ρ|=1} m(ρ)².
  - Published in Sovrem. Probl. Mat. 16 (2012) 38–44, translated in Proc. Steklov Inst. Math. 280 (2013), suppl. 2, 30–36 — [Crossref record, DOI](https://doi.org/10.1134/S0081543813030036).
- **How Burnol's lower bound is proved (read in his full text)** — [Burnol](https://arxiv.org/abs/math/0103058).
  - The Mellin transform gives a Plancherel isometry onto L² of the critical line.
  - Z(s) = ((s−1)/s)(ζ(s)/s) lies in H². Its inverse Mellin transform is A(t) = [1/t] log t + log([1/t]!) + [1/t].
  - He uses the "Báez-Duarte" invariant unitary operator V with multiplier (s/(1−s))³ ζ(1−s)/ζ(s), so V = (1−M)²U. Then D(λ) is the distance from χ_1(t) = (1 + log t)χ(t) to C_λ = span{D_θ A : λ ≤ θ ≤ 1}.
  - Thm 4.2: he defines Y^λ_{s,k} = l.i.m._{w→s} V^{−1}Q_λV(ψ_{w,k}), with ψ_{w,k}(t) = (log(1/t))^k t^{−w} χ(t). These satisfy (D_θ(A), Y^λ_{s,k}) = −(d/ds)^k θ^{s−1/2} Z(s) for λ ≤ θ ≤ 1.
  - Cor. 4.4: Y^λ_{s,k} ⊥ C_λ iff ζ^{(j)}(s) = 0 for all j ≤ k, that is, iff s is a zero ρ and k < m_ρ.
  - He then computes "the exact asymptotics of the orthogonal projection of χ_1 to the vector spaces spanned by the X^λ_{ρ,k}, for a finite set of roots, exactly as in the Grenander–Rosenblatt method". After normalisation the vectors for distinct zeros "become perpendicular" as λ → 0.
  - Toy model (Thm 2.1): for Q(z) = Π_α(1 − ᾱz)^{m_α} with all roots on the unit circle, E(N) = inf_{deg A≤N} ∫|1 − QA|² dθ/2π satisfies lim N·E(N) = Σ_α m_α². E(N) is the squared norm of the projection of 1 onto the q-dimensional orthogonal complement of the multiples of Q. That complement is spanned by kernel-type vectors Y^N_{α,k} at the roots. After rescaling, their Gram matrix splits into Cauchy blocks (1/(i+j+1)), one per root, and the top-left entry of each inverse block is m_α².
- **Dimitrov–Oliveira make the interpolation structure explicit** (unconditional) — [Dimitrov–Oliveira, full text](https://arxiv.org/abs/1608.07887).
  - Problem 2: minimise ∫|B(1/p+it)|² dt/(1/p²+t²) over Dirichlet polynomials B of length n with B(1/p + it_j) = 1 for j = 1..m. They motivate this by noting that every 1 − L(s,χ)A_n(s) "take[s] value one at the zeros".
  - Thm 3: for distinct t_j and n > n(m) the minimiser is unique, and d²_{n,m,p} ∼ (1/log n) Σ_{j≤m} 1/(1/p² + t_j²).
  - For p = 2 and the t_j the ordinates of distinct critical zeros, d²_{n,m,2} ∼ (1/log n) Σ_{j≤m} 1/|ρ_j|². They note "the similarity with the conditional result of BCF is amazing".
  - They also record that Báez-Duarte proved the plain partial sums Σ_{k≤n} μ(k)k^{−s} do not make d_n → 0.
- Survey: [Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the RH", arXiv:math/0607733 (Proc. Indian Acad. Sci. 116 (2006))](https://arxiv.org/abs/math/0607733).

### Inferences
- **Lower bounds are interpolation-type, not sampling-type.** The approximant 1 − ζA_N equals 1 at every zero. The distance is therefore at least the minimal norm of a function in a reproducing-kernel space taking prescribed values at finitely many zeros. That minimum is computed from the inverse of the finite Gram matrix of the kernel vectors at those zeros. For a fixed finite set of zeros and N → ∞ these kernels become orthogonal, and each zero contributes ≈ 1/(|ρ|² log N).
- **This is the opposite regime from the corollary.** The corollary needs zeros dense relative to the Dirichlet-polynomial length: T ≥ e^24 N, about (T/π) log T zeros against N coefficients. That gives a lower frame (sampling) bound. NB uses a fixed finite set of zeros against N → ∞, the asymptotic Riesz-sequence (interpolation) regime. These are the two sides of the Beurling–Landau sampling/interpolation dichotomy.
- **Different quantities.** NB bounds the distance of one fixed vector (d_N² ≍ 1/log N, conjecturally). The corollary bounds the worst-case Rayleigh quotient (λ_N ≥ c/N, numerically ≍ log N/N). Neither implies the other.
- **Same constant on the diagonal.** The diagonal entry of Q_N is n·K(1), with K(1) = Σ_ρ 1/(ρ(1−ρ)) = 2Σ_ρ 1/ρ = 2 + γ − log 4π ≈ 0.0462. This is the BBLS/BCF constant, and under RH it equals Σ m_ρ/|ρ|². So tr Q_N = (2+γ−log 4π)·N(N+1)/2 (computed here).
- **Do not read anything into 0.048 ≈ 0.0462.** The numerical coefficient 0.048 in λ_N ≈ 0.048 log N/N is close to 0.0462, and also to 1/(2π²) ≈ 0.0507. No source found connects λ_N to either constant.
- Burnol's constant Σ m_ρ²/|ρ|² ≥ Σ m_ρ/|ρ|² = K(1) under RH, with equality iff all zeros are simple. If Q_N is defined with multiplicity, it carries weights m_ρ, not m_ρ².

### Gaps
- I did not read BBLS 2000 itself. Burnol (sum over all zeros counted once; trivial if RH fails) and BCF (distinct zeros on the critical line; "unconditionally") restate it slightly differently. I also did not see BBLS's original proof, which uses their "Lemme 6"; Burnol relies on it.
- I found no explicit-in-N (effective) version of the BBLS/Burnol lower bounds; both are lim inf statements.
- Landreau–Richard's numerics (Exp. Math. 2002) were not read. They may contain conditioning or eigenvalue data for the NB Gram matrix.

## Q2. Weil's quadratic form under support constraints, Li coefficients: smallest eigenvalues and how they behave as the window grows

### Takeaway
On test functions supported in [λ^{−1}, λ] (log-variable window [−L, L], L = log λ), the Weil form behaves in three regimes:
- **Small windows:** it is positive, and its lowest eigenvalue tends to +∞ like log(1/a) as the window shrinks (Yoshida; Connes–Consani; Suzuki 2026).
- **Growing windows:** its smallest eigenvalues become extremely small. Connes–Consani found 2.389 × 10⁻⁴⁸ at λ² = 11, with log of the smallest eigenvalue decaying roughly linearly in λ². A 2026 preprint fits −ln λ_min ≈ 2π² N(T*)/ln N(T*) with T* = 2πe^{2L}, and proves λ_min(L) ≤ exp(−L e^L) under RH.
- **Mechanism:** near-radical "prolate vectors" E(f)(x) = x^{1/2}Σ_n f(nx), whose Mellin transforms contain the factor ζ(s).

Li coefficients are not eigenvalues. They grow like (n/2) log n under RH.

### Cited Findings
- **Weil's criterion in Connes–Consani's normalisation.** The explicit formula reads f̃(0) − Σ_{ρ∈Z} f̃(ρ) + f̃(1) = Σ_v W_v(f). RH holds iff Σ_v W_v(g ∗ ḡ^♯) ≤ 0 for all g ∈ C_c^∞(ℝ_+^*) with g̃(z) = 0 for z in a finite set F ⊃ {0,1}, F ∩ Z = ∅ (their App. C, Prop. C.1). For compactly supported f the right side "involves only finitely many primes" — [Connes–Consani, "Weil positivity and trace formula, the archimedean place", arXiv:2006.13771, full text; Selecta Math. 27 (2021), no. 4](https://arxiv.org/abs/2006.13771) ([DOI](https://doi.org/10.1007/s00029-021-00689-4)).
- **Yoshida 1992, as restated by Connes–Consani 2021.** "For any smooth, positive definite function f with support in the interval (1/2, 2) and whose Fourier transform vanishes at ±i/2 one has W_∞(f) ≥ 0." This "was proved in [Yoshida] by reducing it to an explicit computation". It is equivalent to positivity of QW(g) = W_∞(g∗g^*) for smooth g supported in [2^{−1/2}, 2^{1/2}] with ĝ(i/2) = 0. No prime contributes in that range — [CC 2021](https://arxiv.org/abs/2006.13771).
  - Reference: H. Yoshida, "On Hermitian forms attached to zeta functions", Adv. Stud. Pure Math. 21 (1992) 281–325 (not read).
  - CC 2023 say Yoshida showed positivity "for λ = 2 using numerical analysis"; here λ is the endpoint of the support of the autocorrelation — [CC 2023, full text](https://arxiv.org/abs/2106.01715).
- **Yoshida 1992, as restated by Suzuki 2026.** Yoshida studied positive definiteness of QW on C_c^∞(−a,a) and observed that RH is equivalent to positive definiteness for every a > 0 — [Suzuki, "Weil's quadratic form via the screw function", arXiv:2606.09096 (2026 preprint), full text](https://arxiv.org/abs/2606.09096).
  - [Prop. 1]: QW(v) ≥ 0 for all nonzero odd v implies RH; the same for all even v implies RH except for possible real zeros.
  - [Lemma 2]: the infimum of QW(v)/‖v‖² over K(a), the restrictions to [−a,a] of smooth 2a-periodic functions, is positive for sufficiently small a.
  - [Lemma 3]: the same holds on finite-codimension subspaces K_N(a).
  - [Thm 2]: non-degeneracy of QW on the completion of K(a) is equivalent to RH.
- **Bombieri, as restated by Suzuki 2026.** References: Rend. Lincei (9) 11 (2000) 183–233, and "A variational approach to the explicit formula", CPAM 56 (2003) 1151–1164 ([DOI](https://doi.org/10.1002/cpa.10089)) — [Suzuki](https://arxiv.org/abs/2606.09096).
  - Bombieri minimised the Rayleigh quotient on H_0^1(−a,a) and on L²(E), E a finite union of intervals, and proved existence of a minimiser ([2000, Thm 3]; [2003, Thm 4.3]).
  - His claimed continuity in a of the even/odd lower bounds ([2000, Thm 5]) "calls for a more careful analysis" according to Suzuki.
- **Connes–Consani 2021, Thm 1.** For g ∈ C_c^∞(ℝ_+^*) supported in [2^{−1/2}, 2^{1/2}] with ĝ(i/2) = ĝ(0) = 0: W_∞(g∗g^*) ≥ Tr(ϑ(g) S ϑ(g)^*). Here S projects L²(ℝ)^{ev} onto the Sonin space, the functions that vanish together with their Fourier transform on [−1, 1] — [CC 2021](https://arxiv.org/abs/2006.13771).
  - Thm 6.11: there is c with 13 < c < 17 such that W_∞(g∗g^*) ≥ Tr(ϑ(g)Sϑ(g)^*) − c|ĝ(0)|² whenever ĝ(i/2) = 0.
  - The difference between the Weil distribution and the Sonin trace is controlled "as a key device [by] the theory of hermitian Toeplitz matrices".
- **Connes–Consani, "Spectral triples and ζ-cycles"** (Enseign. Math. 69 (2023) 93–148) — [arXiv:2106.01715, full text](https://arxiv.org/abs/2106.01715) ([DOI](https://doi.org/10.4171/LEM/1049)).
  - **Archimedean place alone.** It "ceases to be positive in the upper part of the interval log(λ²) ∈ [log 2 − 0.2, log 2 + 0.2]". Adding p = 2 restores positivity.
  - **Sensitivity to the primes.** Requiring positivity pins p to an interval of size ~10⁻³ around 2. Ignoring a prime power once λ² passes it destroys positivity (shown up to λ² ~ 7).
  - **At L = log 2:** the smallest eigenvalue of the archimedean even matrix is ∼ 0.00133 (Fig. 5).
  - **Extremely small eigenvalues.** As λ grows, the operator on L²([λ^{−1},λ], d^*u) "admits a finite number of extremely small positive eigenvalues… when λ² = 11 the smallest positive eigenvalue is 2.389 × 10⁻⁴⁸".
  - **Decay rate.** For the smallest eigenvalue s(L), "one finds an exponential behavior": log s(L) is plotted against µ = exp L (Figs 18–19; plots only, no fitted constant). The number of small eigenvalues "increases roughly like µ = exp L" (Fig. 20).
  - **Mechanism.** The radical of the Weil form contains the range of E(f)(x) = x^{1/2}Σ_{n>0} f(nx), for f even Schwartz with f(0) = f̂(0) = 0. Poisson summation gives E(f̂)(x) = E(f)(x^{−1}). The cutoff projections satisfy P_λ ∩ P̂_λ = {0}, but their angle operator has 1 + ν(λ²) ∼ 2λ² extremely small nonzero eigenvalues, with prolate spheroidal eigenfunctions (Slepian–Pollak). Restricting E(f) to [λ^{−1},λ] gives "prolate vectors" on which QW_λ is "non-zero, but extremely small".
  - Cor. 2.4: the lower bound of QW_λ is the N → ∞ limit of the smallest eigenvalue on the span E_N of U^k (finite matrices σ^±).
- **Zhu 2026 (arXiv preprint, v2; revised, includes a retraction of an earlier claim; unrefereed)** — [arXiv:2608.24827, abstract and text excerpts](https://arxiv.org/abs/2608.24827).
  - Defines λ*(L) = inf Q(f)/‖f‖₂² over even real f supported in [−L, L], with Q evaluated on f ⋆ f̃. Under RH, Q(f) = Σ_{γ>0} 2|f̂(γ)|².
  - Certified lower bound: Q(f) ≥ 8.9 × 10⁻¹⁸‖f‖² for supp f ⊆ [−0.8, 0.8], 2.3 times the classical range [−(log 2)/2, (log 2)/2].
  - Certified unconditional variational upper bounds, down to 3.2 × 10⁻²⁸³ at L = 2. Combined: 8.9 × 10⁻¹⁸ ≤ λ*(0.8) ≤ 2.27 × 10⁻¹⁷.
  - Empirical law: −ln λ_min(L) ∼ 2π² N(T*)/ln N(T*), with T* = 2πe^{2L}. The constant "is fitted, not derived"; 2π² matches the Landau–Widom eigenvalue-plunge rate.
  - Thm 1.3 (assuming RH): there is L_0 with λ*(L) ≤ exp(−L e^L) for all L ≥ L_0. The proof multiplies a finite canonical product over zeros up to T = 2πe^L by a power-of-sinc window.
- **Suzuki 2026, own results** (unconditional; preprint) — [Suzuki](https://arxiv.org/abs/2606.09096).
  - Thm 1.3: the lowest eigenvalue λ_a of the self-adjoint operator A_a of QW on L²(−a,a) is continuous in a. This re-proves Yoshida's equivalence: RH holds iff QW^a is nondegenerate for every a.
  - Thm 1.4: for small a > 0, λ_a is positive and simple, with λ_a = log(1/a) + µ_1 − log(2π) + ψ(2) − 1 + O(a) as a → 0⁺ (µ_1 > 0 a constant), and the eigenfunction is even.
  - He attributes to Connes–Consani–Moscovici: QW^a is lower bounded and lower semicontinuous; A_a has discrete, lower-bounded spectrum and a ground state; on certain finite-dimensional subspaces, the Fourier transform of the lowest eigenfunction has only real zeros ([CCM, "Zeta spectral triples", Thm 3.6, Cor 3.7, Thm 5.10]).
- **Connes–van Suijlekom (Commun. Math. Phys. 406 (2025))** — [arXiv:2511.23257, abstract](https://arxiv.org/abs/2511.23257) ([DOI](https://doi.org/10.1007/s00220-025-05493-1)).
  - Carathéodory–Fejér corollary: if T ∈ M_n(ℂ) is Hermitian, positive semidefinite, Toeplitz, of rank n−1, and ξ ∈ ker T, then Σ ξ_j z^j has all its zeros on the unit circle.
  - Continuous analogue: if the form with kernel D̃(x−y) is lower bounded on L²([−L/2, L/2]), and its lowest spectral value is a simple isolated eigenvalue with even eigenfunction ξ, then all zeros of ξ̂ are real.
- **Connes–Consani–Moscovici, "Zeta spectral triples"** — [arXiv:2511.22755, abstract](https://arxiv.org/abs/2511.22755); EMS Ser. Lect. Math. (2026) 39–76 ([DOI](https://doi.org/10.4171/elm/37/3)).
  - They take rank-one perturbations of the scaling spectral triple on [λ^{−1},λ], using only Euler factors for p ≤ x = λ².
  - The spectra match the lowest zeros "with striking numerical accuracy". "A rigorous proof of this convergence would establish the Riemann Hypothesis."
- **Related spectral realisations (not eigenvalue bounds).**
  - [CCM, "Zeta zeros and prolate wave operators", Ann. Funct. Anal. 15 (2024)](https://arxiv.org/abs/2310.18423) ([DOI](https://doi.org/10.1007/s43034-024-00388-z)): semilocal prolate operator; positive spectrum ↔ low-lying zeros, Sonin space ↔ UV behaviour.
  - [Connes–Moscovici, arXiv:2112.05500; PNAS 119 (2022)](https://arxiv.org/abs/2112.05500): negative eigenvalues reproduce the UV behaviour of squared zeros.
  - [Suzuki, arXiv:2610.32704 (Oct 2026)](https://arxiv.org/abs/2610.32704): under RH, the positive eigenvalues of a distinguished self-adjoint extension of d/dx on the Hilbert space of the localized Weil form converge to the distinct positive ordinates of the zeros as the interval grows.
- **Li's criterion.** λ_n = Σ_ρ[1 − (1 − 1/ρ)ⁿ], and RH holds iff λ_n ≥ 0 for all n ≥ 1 — [X.-J. Li, J. Number Theory 65 (1997) 325–333](https://doi.org/10.1006/jnth.1997.2137), as described in [Lagarias, arXiv:math/0404394, full text](https://arxiv.org/abs/math/0404394).
  - **Bombieri–Lagarias** ([J. Number Theory 77 (1999) 274–287](https://doi.org/10.1006/jnth.1999.2392)), as described by Lagarias:
    - A Li criterion holds for general multisets Z: if Z omits 0 and 1 and is invariant under ρ ↦ 1−ρ̄, then Re λ_n(Z) ≥ 0 for all n > 0 forces Re ρ = 1/2 for every ρ ∈ Z.
    - An explicit-formula expression for λ_n.
    - If RH fails, the "incomplete" term is sometimes exponentially large in n.
  - **Lagarias** ([Ann. Inst. Fourier 57 (2007) 1689–1740](https://arxiv.org/abs/math/0404394)) relates λ_n to values of Weil's quadratic functional. Under RH, λ_n = (n/2) log n + C_1 n + O(√n log n).
  - **Keiper.** His coefficients equal (1/n)λ_{−n}. His Figure 1 plots λ_{−n} − [(1/2)n log n + (1/2)(γ − 1 − log 2π)n] for 1 ≤ n ≤ 7000, indicating |S_f(n)| < 20 — [Keiper, Math. Comp. 58 (1992), no. 198](https://doi.org/10.1090/S0025-5718-1992-1122072-5), via [Lagarias](https://arxiv.org/abs/math/0404394).
  - **Suzuki 2023:** RH holds iff all Li coefficients are norms of certain concrete functions in a model space, "a kind of Weil's criterion" — [Suzuki, J. Number Theory 252 (2023) 177–194, abstract](https://arxiv.org/abs/2301.05779) ([DOI](https://doi.org/10.1016/j.jnt.2023.05.007)).

### Inferences
- **Order-of-magnitude comparison.** In the window problem, the smallest eigenvalue is super-exponentially small in the window size. Matching the window [−L, L] (type L) to frequencies log n ∈ [0, log N] gives e^{2L} ↔ N. Zhu's empirical law then corresponds to λ ≈ exp(−c·N(2πN)/log N) ≈ exp(−cN). The proven λ_N ≥ c/N and the numerical λ_N ≍ log N/N are polynomial in N.
- **Why the difference.**
  - In the window problem the norm is ‖f‖₂² = (1/2π)∫|f̂|². Prolate/Slepian concentration lets f̂ put its mass below T* = 2πe^{2L}. There the zero density (1/2π) log(t/2π) is below the Landau sampling density L/π for type-L functions, so Σ_γ |f̂(γ)|² can be tiny.
  - In the corollary the norm is the coefficient norm Σ x_n² ≤ Σ x_n² n, the mean square of an almost-periodic Dirichlet polynomial, whose mass cannot concentrate below any height. Above the analogous threshold t ≈ 2πN, where (1/2π) log(t/2π) passes the Nyquist rate (log N)/2π, the zeros sample D. Their weights 1/(1/4+γ²) ≈ 1/N² then give a lower bound polynomial in 1/N.
  - The same threshold T* = 2π·(e^{2L} ↔ N) appears in both settings. The corollary's e^24 N is a large constant multiple of this natural threshold.
- **Consistency check (computed here).** At λ² = e^{2L} = 11: T* = 2π·11 ≈ 69.1, and there are N(T*) = 16 zeros below it (γ_16 ≈ 67.08, γ_17 ≈ 69.55). Then 2π²·16/ln 16 ≈ 113.9, against −ln(2.389 × 10⁻⁴⁸) ≈ 109.6 from Connes–Consani's value. The two independent sources agree to about 4%.
- **Radical vectors versus truncations.** The prolate vectors are almost in the radical because their Mellin transforms carry the factor ζ: the map E(f) = x^{1/2}Σ_n f(nx) is the co-Poisson/Müntz structure also used in the Nyman–Beurling setting. In the corollary, the analogous near-radical vectors are Dirichlet polynomials that are small at the low zeros, for example truncated alternating zeta sums (Q3). Sharp truncation at n ≤ N costs only polynomially, consistent with λ_N ≍ polylog(N)/N rather than super-exponential smallness.
- **No small-window analogue.** Small windows have a large lowest eigenvalue, λ_a ∼ log(1/a) (Suzuki 2026), because the archimedean singularity dominates. The corollary's λ_N is governed by long Dirichlet polynomials.

### Gaps
- Yoshida 1992 and Bombieri 2000/2003 were not read directly; their statements come from Connes–Consani 2021 and Suzuki 2026. No size of Bombieri's minimal eigenvalue was found.
- No peer-reviewed rigorous asymptotic for the smallest eigenvalue of the Weil form on [λ^{−1}, λ] as λ → ∞ was found. Connes–Consani's statements are numerical. Zhu's two-sided bounds, empirical law and conditional Thm 1.3 are in an unrefereed 2026 preprint. Suzuki 2026 is also a preprint.
- Connes–Consani's decay plots (Figs 18–21) give no fitted constant; only the λ² = 11 value and the L = log 2 archimedean value are quoted numerically.
- Other 2026 arXiv items were seen and not assessed or relied on: [Kim et al., arXiv:2607.24830](https://arxiv.org/abs/2607.24830), which claims a numerical realisation of "Suzuki's Weil-quadratic-form operator" with a superexponentially decaying positive lowest eigenvalue, and [Desogus, arXiv:2609.20367](https://arxiv.org/abs/2609.20367), which claims a positivity argument.

## Q3. Gram/Toeplitz/Hankel matrices indexed by n ≤ N (built from the zeros, from Λ, or from K) with bounded smallest eigenvalue; any result of the form λ_min ≥ c/N or ≫ N^{−A}

### Takeaway
I found no published or preprint result giving a polynomial lower bound (c/N or N^{−A}) for the smallest eigenvalue of an RH-related positive form on N-dimensional test spaces. The literature has:
- explicit formulas for the Nyman–Beurling Gram matrix, with no eigenvalue bounds found;
- finite Galerkin/Toeplitz truncations of the Weil form, whose smallest eigenvalues are tiny (Q2), used qualitatively (real-zero theorems);
- distance lower bounds of order 1/log N, which are not eigenvalue bounds.

As far as this search goes, λ_N ≥ c/N appears to have no direct precedent. It is consistent with an easy upper bound of polylog(N)/N (Inferences).

### Cited Findings
- **Nyman–Beurling Gram matrices.**
  - The quotient-of-Gram-determinants formula for d_n² — [Dimitrov–Oliveira](https://arxiv.org/abs/1608.07887).
  - The multiplicative autocorrelation of {·}, giving the Gram entries, is studied in BBLS 2005, Ramanujan J. 9, 215–240 (title verified, content not read) — [DOI](https://doi.org/10.1007/s11139-005-0834-4).
  - Ehm 2024 derives "formulae for Gram matrices arising in the Nyman–Beurling reformulation", via series S(x) = Σ_n R(nx) with reciprocity relations and decompositions of the associated quadratic forms — [Ehm, arXiv:2405.06349, abstract](https://arxiv.org/abs/2405.06349).
  - Alouges–Darses–Hillion: in a probabilistic generalisation, "the difficulty for proving RH is then reallocated in (ii), which heavily relies on the corresponding Gram matrices". A particular tuning makes the second Gram matrix "a block Hankel form" — [arXiv:2006.02953, abstract](https://arxiv.org/abs/2006.02953).
  - None of these abstracts states a smallest-eigenvalue bound.
- **Finite truncations of the Weil form.**
  - Connes–Consani compute the lower bound of QW_λ as the limit of smallest eigenvalues of finite sections (Cor. 2.4) — [CC 2023](https://arxiv.org/abs/2106.01715).
  - Groskin (2026 preprint): the Connes–van Suijlekom and Connes–Consani–Moscovici truncations "at a prime cutoff c>1 and frequency band N, produce finite Galerkin matrices whose spectra are the finite-rank window on Weil positivity". He claims each value of the truncated form is an exact sum over the zeros — [arXiv:2607.02828, abstract](https://arxiv.org/abs/2607.02828).
  - Toeplitz structure and the Carathéodory–Fejér real-zero theorem — [Connes–van Suijlekom 2025](https://arxiv.org/abs/2511.23257).
- **Sizes of smallest eigenvalues actually reported.**
  - Weil window: 0.00133 (archimedean, L = log 2) and 2.389 × 10⁻⁴⁸ (λ² = 11) — [CC 2023](https://arxiv.org/abs/2106.01715).
  - 8.9 × 10⁻¹⁸ to 2.27 × 10⁻¹⁷ at L = 0.8, ≤ 3.2 × 10⁻²⁸³ at L = 2, and ≤ exp(−Le^L) under RH — [Zhu 2026, preprint](https://arxiv.org/abs/2608.24827).
  - Small windows: λ_a ∼ log(1/a) — [Suzuki 2026, preprint](https://arxiv.org/abs/2606.09096).
- **Identity behind the K-kernel (classical integral, used in the inferences).** For Re s > 0, ∫_0^n u^{s−1} du = n^s/s, so F(s) = Σ_n x_n n^s/s is the Mellin transform of f_x = Σ_n x_n 1_{(0,n]}. The Mellin–Plancherel framework is in [Burnol](https://arxiv.org/abs/math/0103058).

### Inferences
- **Q_N as a Weil-type form.** Under RH, Q_N(x) = Σ_ρ |F(ρ)|² with F the Mellin transform of the step function f_x = Σ_{n≤N} x_n 1_{(0,n]}. So Q_N is formally the zero side of the Weil/Guinand explicit formula for the autocorrelation of f_x. The explicit formula rewrites the entries K(m/n) through prime sums up to max(m/n, n/m) ≤ N and archimedean terms.
  - Compared with Q2, the test space consists of non-compactly supported step functions (support (−∞, log N] in log scale), and the norm is the ℓ² norm of coefficients, not L².
  - Compared with Q1, NB studies |1 − ζA|² on the line, with 1 − ζA equal to 1 at the zeros. Here the Dirichlet polynomial is A(s) = Σ x_n n^s itself, evaluated at the zeros. For real x and under RH, |Σ x_n n^ρ| = |Σ (n x_n) n^{−ρ}|, so Q_N = Σ_ρ |B(ρ)|²/|ρ|² with B(s) = Σ b_n n^{−s} and Σ x_n² = Σ b_n²/n².
- **Likely upper bound (heuristic, not from a source, should be checked).** Take x_n = (−1)^{n−1}/n, so B is the partial sum of η(s) = (1 − 2^{1−s})ζ(s) and Σ x_n² ≈ π²/6.
  - Since η(ρ) = 0, |B(ρ)| ≈ (1/2)N^{−1/2} for |γ| ≲ cN (alternating-series tail).
  - For |γ| ≳ cN, the mean square is Σ b_n²/n = Σ 1/n ≈ log N.
  - Hence Q_N(x) ≲ (1/N)Σ1/|ρ|² + log N·Σ_{|γ|>cN} 1/γ² ≍ (log N)²/N, suggesting λ_N ≪ (log N)²/N under RH. The proven c/N and the numerical ≈ 0.048 log N/N would then be sharp up to logarithms.
- **A Li-coefficient analogue of the corollary (derived here; found in no source).** Under RH, z_ρ = 1 − 1/ρ lies on the unit circle and |1 − z_ρ|² = 1/|ρ|². For c ∈ ℂ^N, Σ_ρ |Σ_{k<N} c_k z_ρ^k|²/|ρ|² = Σ_{j,k} c_j c̄_k t_{j−k}, with t_m = Σ_ρ z_ρ^m/|ρ|² = λ_{m+1} − 2λ_m + λ_{m−1} (using λ_{−m} = λ_m and λ_0 = 0).
  - So the Toeplitz matrices (Δ²λ_{j−k})_{j,k<N} are positive semidefinite under RH. They are the Gram matrices of (z_ρ^k/ρ)_ρ, exactly the corollary's (n^ρ/ρ)_ρ with n^ρ replaced by z_ρ^k.
  - t_0 = 2λ_1 = Σ 1/|ρ|² = 2 + γ − log 4π = K(1).
  - Because the z_ρ accumulate at 1 (arg z_ρ ≈ 1/γ), λ_min of these Toeplitz matrices tends to 0. I found no study of their rate or of this form.
- **Status.** The corollary is conditional on RH, which is what makes Q_N a Gram matrix. Whether "Q_N ⪰ 0 for all N" is itself equivalent to RH, i.e. whether the step-function test family is rich enough for Weil's criterion, was not addressed by any source found.

### Gaps
- No paper found on the smallest eigenvalue or condition number of the Nyman–Beurling Gram matrix (Vasyunin's formula, BBLS 2005, Ehm 2024). Vasyunin's biorthogonal-system paper (St. Petersburg Math. J., mid-1990s) could not be verified via Crossref.
- No paper found on Gram matrices of (n^ρ/ρ)_ρ or (n^{−ρ})_ρ, on the kernel Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)) as a matrix kernel on ratios m/n, or on Hankel/Toeplitz forms built from Λ with eigenvalue bounds.
- The search was limited (arXiv API by title, author and abstract; Crossref; selected full texts). MathSciNet and zbMATH reviews could not be queried, since the zbMATH web search returned no usable results.

## Q4. Riesz-basis, frame and completeness statements: dilation systems and systems indexed by the zeros

### Takeaway
Dilation systems φ(nx) are well understood through the Hilbert space ℋ² of Dirichlet series (Hedenmalm–Lindqvist–Seip), and distances to reproducing kernels localise zeros (Nikolski). Burnol characterised the de Branges–Sonine spaces in which the zeros form complete or minimal systems. I found no Riesz-basis or frame theorem for {n^{−ρ}} or {x^ρ} indexed by the zeros. The corollary's sampling inequality is best described as a lower frame bound for the N exponentials n^{iγ} sampled on zeros up to height ≍ N. That order of height is necessary.

### Cited Findings
- **Hedenmalm–Lindqvist–Seip** (Duke Math. J. 86 (1997) 1–37) — [arXiv:math/9512211, abstract](https://arxiv.org/abs/math/9512211) ([DOI](https://doi.org/10.1215/S0012-7094-97-08601-4); [Addendum, Duke 99 (1999) 175–178](https://doi.org/10.1215/S0012-7094-99-09907-6)).
  - Question: for φ ∈ L²(0,1) extended as an odd 2-periodic function, "when the collection of dilates φ(nx), n=1,2,3,…, constitutes a Riesz basis or a complete sequence in L²(0,1)".
  - The problem "translates into a question concerning multipliers and cyclic vectors in the Hilbert space ℋ of Dirichlet series f(s) = Σ a_n n^{−s}" with square-summable coefficients.
  - ℋ is modelled as H² of the infinite-dimensional polydisk, with vertical-limit functions f_χ.
- **Nikolski** (Ann. Inst. Fourier 45 (1995) 143–159): "a subspace of a holomorphic Hilbert space is completely determined by their distances to the reproducing kernels"; "a simple rule… to localize common zeros of a subspace of the Hardy space of the unit disc"; illustrated by "a series of discs of the complex plan[e] free of zeros of the Riemann ζ-function" — [Numdam, abstract](https://www.numdam.org/item/AIF_1995__45_1_143_0/) ([DOI](https://doi.org/10.5802/aif.1451)). Book treatment: "Distance formulae and zeros of the Riemann ζ-function", Math. Surveys Monogr. 92, 163–171 — [DOI](https://doi.org/10.1090/surv/092/08).
- **Burnol 2004** (J. Théor. Nombres Bordeaux 16, 65–94): links "the Hilbert space properties of the Riemann zeros, the 'dual Poisson formula' of Duffin–Weinberger (also named by us co-Poisson formula), and the 'Sonine spaces' of entire functions defined and studied by de Branges. We determine in which (extended) Sonine spaces the zeros define a complete, or minimal, system." — [Numdam, abstract](https://www.numdam.org/item/JTNB_2004__16_1_65_0/) ([DOI](https://doi.org/10.5802/jtnb.434)).
- **Burnol 2002:** vectors X^λ_{ρ,k} for ζ(ρ) = 0, k < m_ρ, which "in the limit when the parameter λ goes to 0 become perpendicular (when they correspond to distinct zeros)". This is asymptotic orthogonality, proposed as a route to a "Hilbert–Pólya space"; it is not a Riesz-basis theorem — [Burnol](https://arxiv.org/abs/math/0103058).
- **Bondarenko–Radchenko–Seip:** "Fourier interpolation bases for functions analytic in a strip", with examples built on the nontrivial zeros of ζ and other L-functions, and a duality principle via kernels of general Dirichlet series — [arXiv:2005.02996, abstract](https://arxiv.org/abs/2005.02996).
- **Operator-theoretic variants of the Báez-Duarte criterion.**
  - Manzur–Noor–Santos: the semigroup W_n f(z) = (1+z+…+z^{n−1}) f(zⁿ) on H²(𝔻) is related to RH, the invariant subspace problem and the periodic dilation completeness problem; several basic questions about it are equivalent to RH — [arXiv:2111.05398; J. Math. Anal. Appl. 525 (2023) 127261](https://arxiv.org/abs/2111.05398).
  - Probabilistic NB criteria — [Darses–Hillion, Confluentes Math. 13 (2021) 43–59](https://arxiv.org/abs/1805.06733).

### Inferences
- **Frame-theoretic phrasing.** In the language of these works, the corollary's inequality Σ_{|γ|≤T} |Σ_{n≤N} y_n n^{iγ}|² ≥ (T/100) Σ|y_n|² (with y_n = √n x_n) says: for T ≥ e^24 N, the zero ordinates in [−T, T] form a sampling set, with lower frame constant ≍ T, for the N-dimensional space of Dirichlet polynomials with frequencies in [0, log N]. The interpolation results of Burnol and Dimitrov–Oliveira are the complementary regime: a fixed finite set of zeros is asymptotically a Riesz sequence of kernels as the length goes to infinity.
- **The threshold T ≍ N is necessary (my argument; uses the classical approximation ζ(s) = Σ_{n≤x} n^{−s} − x^{1−s}/(1−s) + O(x^{−σ}) for |t| ≤ 2πx/C, Titchmarsh Thm 4.11, not re-verified this session).** Take y_n = n^{−1/2}. Under RH, Σ_{n≤N} n^{−1/2+iγ} = conj(Σ_{n≤N} n^{−ρ}) ≈ N^{1−ρ̄}/(1−ρ̄) at zeros with |γ| ≤ 2πN/C. So the left side is ≈ N·Σ_ρ 1/|ρ|² = O(N) when T = κN, while the right side is ≍ κN log N. The sampling inequality therefore fails for fixed small κ and large N. A height threshold of order N is necessary, and the open question is only the constant (e^24 versus something near 2π).
- **Status.** No source gives a Riesz basis or frame for {n^{−ρ}} over all zeros. A finite-N, finite-T sampling statement with explicit constants, as in the corollary, appears not to be in this literature.

### Gaps
- Not verified from the full text: HLS's exact Riesz-basis criterion (believed to be "S_φ and 1/S_φ bounded analytic", unconfirmed); Nikolski's specific zero-free discs; Burnol 2004's exact spaces and parameters.
- Sampling and interpolation theory for spaces of Dirichlet series (e.g. Olsen–Seip) and large-sieve and mean-value inequalities at zeros (Montgomery, Gonek, Landau's formula) were outside this assignment and not checked here. They are the natural places to look for direct precedents of the sampling inequality.
