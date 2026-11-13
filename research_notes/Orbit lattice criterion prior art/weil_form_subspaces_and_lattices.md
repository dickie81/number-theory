# Weil's form on finite-dimensional test spaces, Gram–Schmidt pivots and lattices: prior art for the orbit criteria (A) and (B)

Scope and conventions. The claims under test are:
- (A) RH ⟺ every Gram–Schmidt pivot d_k of the orbit vectors w_1, w_2, … satisfies d_k ≥ d_1 = K_H(1) = 2 + γ − log 4π;
- (B) RH ⟺ w_1 is a shortest nonzero vector of the integer lattice spanned by the w_n.

Here G_N = (√(mn)·K_H(m/n))_{m,n≤N} and K_H(r) = Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)).

This note extends `research_notes/Sampling Dirichlet polynomials at zeta zeros/gram_and_nyman_beurling.md`. It does not repeat that note's Nyman–Beurling, window-eigenvalue, Li-coefficient and Riesz-basis material.

Source tags:
- **full text**: I read the PDF this session (BDIM or arXiv).
- **zbMATH review**: I read only the Zentralblatt review, fetched through the zbMATH Open API.
- **as restated by X**: I did not read the primary source.

Anything marked "(computed here)" or listed under Inferences is my own derivation.

## Q1. Yoshida 1992: what is proved about Weil's form on spaces of test functions, and are there pivot or margin statements?

### Takeaway
Yoshida localised Weil's criterion to test functions supported in an interval [−a, a] (log scale). He proved three kinds of result about it:
- unconditional positivity for small windows;
- a quantitative **margin on a finite-codimension subspace**: high Fourier modes are positive with any prescribed margin µ, which reduces positivity on a window to a finite computation;
- RH-equivalents phrased as non-degeneracy of the form on completed spaces.

He verified positivity numerically for the window of length log 2. No Gram–Schmidt, pivot, Cholesky or lattice statement appears in any of the three accounts I read. I could not read the paper itself.

### Cited Findings
- **Bombieri's summary of Yoshida (Bombieri 2000, §1).**
  - "A first study of Weil's functional was done by H. Yoshida [5] in 1992. In his paper, Yoshida studies the behaviour of the associated hermitian form in certain Hilbert spaces of functions supported in an interval [−t, t], obtaining several interesting results."
  - Besides reproving Weil's criterion, "he shows that the positivity of the functional in the class of smooth even functions with compact support is equivalent to the validity of the Riemann hypothesis excluding real zeros. Moreover, he shows how the positivity of this functional for functions supported in a fixed interval [−t, t] can be reduced to a finite calculation (depending on t), and verifies this positivity for t = (log 2)/2."
  - Source: [Bombieri, Rend. Mat. Acc. Lincei (9) 11 (2000) 183–233, full text (BDIM)](http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0).
- **Suzuki's account of Yoshida, with Yoshida's numbering.** Source: [Suzuki, "Aspects of the screw function corresponding to the Riemann zeta-function", arXiv:2206.03682, full text; J. London Math. Soc. (2) 108 (2023) 1448–1487](https://arxiv.org/abs/2206.03682) (journal data from [zbMATH 1536.11133](https://zbmath.org/?q=an:1536.11133)).
  - **Spaces.**
    - C(a) = {φ ∈ C_c^∞(ℝ): supp φ ⊂ [−a, a]} "was first introduced by him to localize the positivity".
    - K(a) consists of the restrictions to [−a, a] of smooth 2a-periodic functions, extended by 0 outside.
    - K_N(a) consists of the ψ ∈ K(a) whose Fourier coefficients ∫ψ(x)exp(πinx/a)dx vanish for |n| ≤ N.
  - **[Yoshida, Lemma 2].** Without any assumption, ⟨·,·⟩_W is positive definite on K(a) for a sufficiently small.
  - **[Yoshida, Lemma 3], the margin statement.** "For given a_0 > 0 and µ > 0, there exists N ≥ 0 such that ⟨φ, φ⟩_W ≥ µ‖φ‖_{L²} for every φ ∈ K_N(a) and 0 < a ≤ a_0". This is transcribed as Suzuki prints it; presumably the squared norm is meant.
  - **[Yoshida, (5.17), (5.18)], the Gram matrix of the Fourier basis.** For χ_n(x) = e^{πinx/a}, |⟨χ_m, χ_n⟩_W| ≪ |m − n|^{−1} for m ≠ n, and ⟨χ_n, χ_n⟩_W ∼ log|n|.
  - **RH-equivalent.** Let \widehat{K_N(a)} be the completion of K_N(a) for ⟨·,·⟩_W, and set \widehat{K(a)} = W(a) ⊕ \widehat{K_N(a)}. "Yoshida proved that the RH is true if and only if ⟨·,·⟩_W is non-degenerate on \widehat{K(a)} for every a > 0."
  - **Unconditional non-degeneracy.** "He proved that ⟨·,·⟩_W is non-degenerate on C(a) and K(a) for every a > 0 ([33, Propositions 2 and 7])."
  - **Priority of the compact-support form.** "Weil does not mention that it is sufficient to taking compactly supported functions as test functions … but in Yoshida [33], the criterion has been formulated in the form above, although it is not sure whether it is the first literature."
- **Yoshida's Theorem 1, as restated by Connes.** "For any smooth, positive definite function f with support in the interval (1/2, 2) and whose Fourier transform vanishes at ±i/2 one has: W_∞(f) ≥ 0." Connes adds: "The proof is a numerical analysis of the positivity of the Weil functional W_∞ restricted to the interval [1/2, 2], and therefore it does not provide any conceptual reason for this positivity that would have a chance to continue to hold when primes are involved." Sources: [Connes, "The Riemann Hypothesis: Past, Present and a Letter Through Time", arXiv:2602.04022 (2026), full text](https://arxiv.org/abs/2602.04022); the same statement appears in [Connes–Consani 2021, full text](https://arxiv.org/abs/2006.13771).
- **zbMATH review of Yoshida (M. Muro).** It describes RH as "reduced to the positive definiteness of an Hermitian form" on C(a). It says "the author deforms the Riemann's hypothesis to the positive definiteness of a 'deformed' function space \widehat{K(a)} … Though he succeeded in proving the positive definiteness of the deformed Hermitian forms on C(a) and K(a), it may require more ideas to prove it on \widehat{K(a)}." Source: [zbMATH 0817.11041, review](https://zbmath.org/?q=an:0817.11041).
  - This conflicts mildly with Suzuki, who reports **non-degeneracy** (not positive definiteness) on C(a) and K(a) for every a, and positive definiteness only for small a.
- **Burnol 2000.** He gave another small-support verification: "The author checks Weil's positivity condition for those functions supported on the intervals [1/c, c]" (zbMATH review; the admissible range of c is not stated there). Source: [Burnol, C. R. Acad. Sci. Paris 331 (2000) 423–428, zbMATH 0992.11064 review](https://zbmath.org/?q=an:0992.11064).

### Inferences
- **What Yoshida's finite calculation is.** His object is the Gram matrix of the **Fourier basis on a window** under the Weil form. Its diagonal grows like log|n| and its off-diagonal entries decay like 1/|m − n|, so the high-mode block is diagonally dominant (Lemma 3). Positivity on the window therefore reduces to positive definiteness of a finite Schur complement.
- **How it differs from (A).**
  - Yoshida's margin holds on a finite-codimension subspace of a window, in the L² norm, and is used to *reduce* positivity to finitely many modes.
  - (A) is a margin on a nested sequence of finite-dimensional spaces span(w_1, …, w_k), with test functions the step functions 1_{(0,n]}, i.e. point masses at log n on the Mellin side.
  - (A) measures against a fixed value d_1 and is uniform in k.
- **No closer statement in these accounts.** No account mentions Gram–Schmidt, pivots, Cholesky factors, determinants of the Weil Gram matrix, lattices or integrality in Yoshida's paper.

### Gaps
- **Not read directly.** I did not read Yoshida's paper. Project Euclid's PDF was blocked by bot protection (an HTML challenge page was returned). Everything above is from Bombieri 2000, Suzuki 2023, Connes 2021/2026 and the zbMATH review.
- **Unresolved points.**
  - The precise statements of his Lemma 3 (norm or squared norm).
  - His Propositions 2 and 7.
  - Whether he ever writes the Gram matrix ⟨χ_m, χ_n⟩_W explicitly with numerical pivots or determinants.

## Q2. Bombieri 2000 and 2003: the functional on finite-dimensional spaces, minima, extremals, and any margin comparable to (A)

### Takeaway
Bombieri 2000 (read in full) has three strands:
- **Variational:** the Weil functional on windows attains its minimum (Theorems 3–4), and the even and odd infima are continuous decreasing functions of the window (Theorem 5).
- **Finite matrices indexed by the zeros:** he passes to finite matrices H(Γ; t) indexed by finitely many **zeros**. Their inertia counts the zeros off the line: the number of negative eigenvalues equals the number of off-line conjugate pairs (Theorem 8), and 0 is an eigenvalue only for repeated zeros (Lemma 10).
- **One explicit margin:** for support of length |I| < log 2 the form is at least (log(1/|I|) − log log(1/|I|) − O(1))·‖F‖² (Theorem 12).

His numerics show that a fake off-line zero produces a negative eigenvalue that tends to 0 at an apparently exponential rate on short windows, so window margins are fragile. Bombieri 2003, known only from its review, studies the extremals of two minimisation problems. Neither paper contains pivots, a margin uniform over nested Dirichlet-polynomial spaces, or any integrality or lattice statement.

### Cited Findings
- **Bombieri 2000: abstract and set-up** (full text) — [Bombieri 2000, BDIM](http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0); [EuDML record](https://eudml.org/doc/252338); [zbMATH 1008.11034](https://zbmath.org/?q=an:1008.11034).
  - **Abstract.** "We prove that this quadratic functional attains its minimum in the unit ball of the L²-space of functions with support in a given interval [−t, t], and prove again Yoshida's theorem that it is positive definite if t is sufficiently small. The Fourier transform of the functional gives rise to a quadratic form in infinitely many variables and we then study its finite truncations and corresponding eigenvalues… if the Riemann Hypothesis is false but only with finitely many non-trivial zeros off the critical line … the number of negative eigenvalues is precisely one-half of the number of zeros failing to satisfy the Riemann Hypothesis, provided the truncation is big enough."
  - **Theorem 1 (strengthened Weil criterion).** RH holds iff Σ_ρ g̃(ρ)·g̃*(1 − ρ) > 0 for every complex-valued g ∈ C_0^∞((0, ∞)) not identically 0. Here g̃* is the Mellin transform of g*(x) = x^{−1}ḡ(1/x).
    - Bombieri's sketch of the converse goes through Li's criterion. g_n is the inverse Mellin transform of 1 − (1 − 1/s)^n, namely P_n(log x) on (0, 1) with P_n(x) = Σ_j C(n,j) x^{j−1}/(j − 1)!.
  - **Theorem 2.** T[f] is defined as ∫f + ∫f* − Σ Λ(n){f(n) + f*(n)} − (log 4π + γ)f(1) − ∫_1^∞(f + f* − 2f(1)/x)·x dx/(x² − 1), and T[f] = Σ_ρ f̃(ρ). RH ⟺ T[f ∗ f̄*] ≥ 0 on C_0^∞((0, ∞)), with equality only for f ≡ 0. "We have in fact proved a little more, namely that the positivity of the Weil quadratic functional is equivalent to the statement that T[g_{n,ε}] > 0 for every positive integer n and ε > 0."
  - **§4, translation invariance.** T[f ∗ f̄*] is invariant under τ_a f(x) = a^{−1/2}f(x/a). Footnote 4 calls τ_a "the analogue of a normalized Frobenius operator", and footnote 3 calls T "an analogue of Weil's definition of trace of a correspondence". Hence "if we try to minimize this functional in the unit sphere of a translation invariant Hilbert space we obtain too many extremals. Thus our Hilbert space cannot be translation invariant by τ_a."
  - **§4, the two problems.**
    - Problem 1 minimises over the unit sphere of W_0^{1,2}([M^{−1}, M]) with norm ‖Df‖, D = x·d/dx.
    - Problem 2 minimises over L²(E), E a finite union of intervals.
- **Bombieri 2000: existence and continuity.**
  - Theorem 3: on L²(E) the infimum is attained.
  - Theorem 4: on W_0, it is attained if it is negative.
  - Theorem 5: the even and odd infima µ±(M) over L²([M^{−1}, M]) are continuous decreasing functions of M.
  - Lemma 1 gives the Euler–Lagrange (variational) equation λ𝒟f = L[f], with an explicit operator L built from Λ(n) and the archimedean kernel.
  - Suzuki 2026 says the continuity claim of Theorem 5 "calls for a more careful analysis" ([as recorded in the earlier note from Suzuki, arXiv:2606.09096](https://arxiv.org/abs/2606.09096)).
- **Bombieri 2000, §§6–8: finite matrices indexed by the zeros.**
  - **The matrix.** Writing ρ = 1/2 + iγ, M = e^t and Λ = 1/λ, the eigenvalue problem becomes w_γ = Λ Σ_{γ′} H(γ, γ′; t) w_{γ′}. Here H(x, y; t) = 2t K*(x, y; t)/(1/4 + y²), K(x) = sin x/x, and D(Λ; t) = det(I − ΛH(Γ_N; t)) (Theorem 6: the resolvent is entire).
  - **The finite model (§8).** For a finite multiset Z closed under ρ ↦ 1 − ρ, ρ ↦ ρ̄, the space V is spanned by Φe^{x/2}, Φe^{−x/2} and Φe^{−iγx} (γ ∈ Γ), where Φ is the indicator of [−t, t]. The form is L[F](x) = Σ_γ ∫F(x + u)e^{iγu}du.
  - **Lemma 10.** "The matrix H(Γ; t) admits the eigenvalue 0 if and only if there is γ ∈ Γ with multiplicity greater than 1… Moreover if every γ is real all eigenvalues of H(Γ; t) are non-negative."
  - **Theorem 8.** "The number of negative eigenvalues of the matrix H(Γ; t) equals the number of distinct complex conjugate pairs (γ, γ̄) in Γ." The acknowledgements say Theorem 8 "was first discovered experimentally with the help of the Mathematica computer package".
- **Bombieri 2000, §§10–11: limits.**
  - **Theorem 10.** If ζ has only finitely many (and at least one) off-line zeros, then for t > 0 there are w_γ with Σ|w_γ|² = 1 and at least 1/2 of the mass on the off-line γ, and λ ≤ 0. Either the associated f gives T[f ∗ f̄*] = λ‖Df‖² < 0, or f ≡ 0. For 0 < t < t_0 (explicitly computable), f must vanish identically.
  - **Corollary to Theorem 11.** If T[f ∗ f̄*] ≥ 0 on E, then "either the Riemann Hypothesis is true, or ζ(s) has infinitely many zeros off the critical line, or the functions x^{−ρ} are linearly dependent over E". The dependence would have coefficients {c_ρ} ∈ ℓ² with at least half the ℓ²-mass on off-line zeros.
  - **Example.** Such relations do occur for pairs of Dirichlet L-functions with the same conductor and gamma factors.
- **Bombieri 2000, Theorem 12: the only explicit margin.** "If F(x) has compact support in an interval I of length |I| < log 2 we have T[F(x) ∗ F(−x)] = Σ_γ F̂(γ)·conj F̂(γ) ≥ (log(1/|I|) − log log(1/|I|) − O(1))·‖F‖²." The text extraction leaves it unclear whether the second logarithm is log⁺.
- **Bombieri 2000, §13: numerics.**
  - **Set-up.** "A fictitious zero off the critical line … set at ρ_0 = 0.52 + i3.14", with the first N zeros, N up to 160. Footnote 11 reports experiments "with k up to 320" zeros.
  - **Finding.** "The numerical evidence … indicates in each case the existence of a critical value t_c^± > 0 such that the unique negative eigenvalue λ_N^±(t) tends to 0 if t < t_c^±, as N → ∞. The rate of convergence is quite fast, suggesting an exponential rate. For t > t_c^± this eigenvalue converges … to a strictly negative value."
- **Bombieri 2003, CPAM 56 (2003) 1151–1164 (zbMATH review only).**
  - The review restates Weil's criterion as T[f ∗ f̄*] ≥ 0, with T[f] = ∫f + ∫f* − Σ_ν W_ν(f) over all places ν ∈ {ℝ, 2, 3, 5, …}.
  - "The author considers the problem of minimization of T[f ∗ f̄*] in two Hilbert spaces and argues that the assumption of the falsity of RH entails unusual consequences for the behaviour of the extremals."
  - Sources: [zbMATH 1048.11070](https://zbmath.org/?q=an:1048.11070); [DOI 10.1002/cpa.10089](https://doi.org/10.1002/cpa.10089).

### Inferences
- **Bombieri works on the zero side.** His finite-dimensional matrices are indexed by finitely many zeros and depend on the window t. G_N is indexed by integers and contains every zero at once through K_H.
- **The nearest analogue is an inertia statement.** By Sylvester's law of inertia, the number of negative eigenvalues equals the number of negative pivots in any LDLᵀ factorisation. So Theorem 8 counts negative pivots of a zero-indexed matrix. (A) asserts the opposite, quantitatively: in the orbit order, every pivot of the integer-indexed matrix stays ≥ d_1 under RH, and some pivot drops below d_1 when RH fails.
- **Window margins are fragile; the orbit margin is not.** On windows, an off-line zero can hide behind a negative eigenvalue that tends to 0 exponentially fast (t < t_c). Positive margins on windows are only available for short supports (Theorem 12, Yoshida's Lemma 3). The orbit criterion has a uniform margin, d_k ≥ 1.249·d_1. It is not a spectral gap, since λ_min(G_N) → 0 (≈ 0.048 log N/N in the earlier report).
- **The orbit vectors are Bombieri's Frobenius translates.** Bombieri avoids τ_a-invariant spaces because the minimiser is not unique there. The orbit construction uses the τ_n-translates themselves:
  - with g = 1_{(0,1]} (Mellin transform 1/s), τ_n g has Mellin transform n^{s−1/2}/s, so w_n = √n·τ_n g (computed here);
  - τ_a-invariance is exactly why ⟨w_m, w_n⟩ depends on m/n alone;
  - Gram–Schmidt in the order n = 1, 2, … breaks the invariance instead of restricting the support.
- **K_H(1) as a Weil value.** Formally, K_H(1) = T[g ∗ g*] for g = 1_{(0,1]}, since f̃(s) = 1/(s(1 − s)) (computed here; g is not smooth, so this is a limiting case of Theorem 2). The constant equals 2λ_1, twice Li's first coefficient, and Nicolas's β (Q4).

### Gaps
- Bombieri 2003 was not read; the Wiley page returned a bot-protection page. Its exact theorems, including Thm 4.3 cited by Suzuki for existence of a minimiser on L²(E), are known only from the review and Suzuki's citation.
- Part II of the 2000 memoir ("…, I" implies a sequel) was not found in zbMATH searches.

## Q3. Connes–Consani (and Moscovici): Weil positivity on [λ^{−1}, λ], smallest eigenvalues and eigenvectors; is there any Gram, Cholesky or lattice formulation?

### Takeaway
Connes–Consani's finite-dimensional devices are of three kinds:
- **Toeplitz discretisations.** They replace ℝ₊* by q^ℤ and the window by its intersection with ωℤ, ω = log q. They analyse the archimedean form with Carathéodory–Fejér-type theorems on positive Toeplitz matrices, and say explicitly that this is "closely related" to Hallouin–Perret's Toeplitz/Gram treatment of RH for curves.
- **Gram–Schmidt as a numerical tool.** They orthogonalise prolate vectors E(φ_n) to build approximate eigenvectors for the extremely small eigenvalues of QW_λ.
- **Hankel/Jacobi (Cholesky-type) structures.** These appear for moment problems of local factors.

None states a pivot lower bound, a Gram–Schmidt margin, or anything involving integer lattices or shortest vectors. Everything is window-restricted and L²-normed.

### Cited Findings
- **Connes–Consani 2021, §6: Toeplitz discretisation of the archimedean form** (full text) — [arXiv:2006.13771; Selecta Math. 27 (2021), no. 4, Paper 77](https://arxiv.org/abs/2006.13771).
  - **Method.** Steps: "1. Discretize the group ℝ₊* by approximating it with q^ℤ, where q → 1+. 2. Identify the approximating operator K_q … as a Toeplitz matrix and compute numerically its eigenvalues. 3. Apply the general theory of Toeplitz matrices to rewrite K_q in canonical form."
  - **The form.** "We replace the interval I = [0, a] by its finite intersection with the lattice ωℤ". The quadratic form is Q_q(ξ) = ω Σ_j Σ_k ξ(j)ξ(j + k)Q(q^{|k|}), with Toeplitz matrix T_q = (Q(q^{|j−k|})).
  - **Numbers.** With ω = 10^{−3}, the largest eigenvalue of the normalised matrix ωT_q is ≈ 1.05177 > 1 on [0, log 2]. The normalising constant is a derivative whose value they give as ≈ 22.9965; its symbol was lost in text extraction. On the symmetric interval of length log 2 the next eigenvalue is ≈ 0.687925, "hence well below 1. Thus the lack of positivity of Id − K_I is due to a single eigenvector".
  - **Toeplitz theory used.** The eigenvector of the extreme eigenvalue has a polynomial with all roots on the unit circle. A positive Toeplitz matrix of co-rank 1 decomposes uniquely into rank-one Toeplitz projections at those roots.
  - **Link to curves.** "The method used in 2. and 3. is closely related to the technique applied in [21] in the context of RH for curves over finite fields", where [21] is Hallouin–Perret, TAMS 372 (2019) 5409–5451 (Q6).
  - **Main inequality.** Thm 6.11, and Thm 1 (W_∞(g ∗ g*) ≥ Tr(ϑ(g)Sϑ(g)*) for support in [2^{−1/2}, 2^{1/2}]), are in the earlier note.
- **Connes–Consani 2023, "Spectral triples and ζ-cycles": Gram–Schmidt of prolate vectors** (full text). "One computes all these components for |j| ≤ N with N large, and applies the Gram–Schmidt orthogonalization process (separately for the even and odd cases) to the obtained vectors in E_N." The result gives "the natural candidate functions to be compared … with the eigenfunctions of the semi-local Weil quadratic form QW_λ" (Definition 3.1 projects onto their span) — [arXiv:2106.01715; Enseign. Math. 69 (2023)](https://arxiv.org/abs/2106.01715).
- **Connes–Consani–Moscovici, "Zeta zeros and prolate wave operators"** (full text) — [arXiv:2310.18423; Ann. Funct. Anal. 15 (2024)](https://arxiv.org/abs/2310.18423).
  - The radical of the Weil form is the range of E(f)(u) = u^{1/2}Σ_n f(nu). Applied to prolate eigenfunctions this "generates extremely small eigenvalues of the Weil quadratic form restricted to functions with fixed compact support. The corresponding eigenfunctions ψ_n … are reconstructed in [11] by Gram–Schmidt orthogonalization of E(φ_n)."
  - The Jacobi-matrix coefficients are a_n = k_n/k_{n+1} with k_n = (D_{n−1}/D_n)^{1/2}, D_n being Hankel determinants of the moments.
- **Connes–Consani–Moscovici, "On q-series and the moment problem associated to local factors"** (full text) — [arXiv:2403.01247 (2024)](https://arxiv.org/abs/2403.01247).
  - The measure is |Π_{v∈S} local factors|² on the critical line, for S = {p, ∞}.
  - Orthogonal polynomials are written as determinants of Hankel matrices.
  - "By the result of A.C. Aitken …, the inverse of the Hankel matrix D(n) is equal to B_n B_n* where B_n is the upper triangular matrix" of orthonormal-polynomial coefficients, a Cholesky-type factorisation.
  - Main result: integrality of the Jacobi coefficients in ℤ[1/√2], explained via Catalan numbers.
- **Connes–Consani, "Quasi-inner functions and local factors"** — [arXiv:2008.10974 (2020), full text](https://arxiv.org/abs/2008.10974). A full-text search found no occurrence of Gram, Toeplitz, Hankel, Cholesky, lattice, pivot or shortest vector.
- **Connes–Consani–Moscovici, "Zeta spectral triples"** — [arXiv:2511.22755, full text](https://arxiv.org/abs/2511.22755). The abstract invokes a generalisation "of the classical Carathéodory–Fejér theorem for Toeplitz matrices". Spectral content is in the earlier note.
- **Connes 2026 survey** (full text) — [arXiv:2602.04022](https://arxiv.org/abs/2602.04022).
  - "A general theorem ensures that whenever the smallest eigenvalue of the corresponding operator is simple and even, the resulting approximating numbers form the spectrum of a self-adjoint operator and hence are all real."
  - Remaining step: "one needs to show that the smallest eigenvalue of the Weil quadratic form QW_λ is simple with even eigenvector."
  - Comparison of eigenvectors for "the first minuscule eigenvalues, using the Gram–Schmidt orthogonalisation of vectors of the form E(ψ)".
  - Weil's proof for curves "used the intersection pairing on divisors and the Hodge index theorem"; on the square of the scaling site "the Frobenius correspondences make sense".
- **Already in the earlier note.** The smallest eigenvalue 2.389 × 10^{−48} at λ² = 11; prolate mechanism; Connes–van Suijlekom's real-zero theorem; Groskin's finite Galerkin truncations ([arXiv:2607.02828](https://arxiv.org/abs/2607.02828)); Zhu's and Suzuki's 2026 preprints. See `gram_and_nyman_beurling.md` Q2–Q3.

### Inferences
- **What the Connes–Consani program uses finite matrices for:**
  - Toeplitz matrices on the cyclic subgroup q^ℤ, a function-field-like discretisation with q → 1;
  - Gram–Schmidt as an algorithm to build approximate minimal eigenvectors;
  - Hankel/Jacobi matrices for moment problems.
- **The orbit matrix lives elsewhere.** G_N is indexed by the multiplicative semigroup ℕ (a free abelian monoid on the primes), not by a cyclic subgroup. It is "multiplicative Toeplitz" (entries depend on m/n), not Toeplitz.
- **Pivots behave differently from eigenvalues.** In Connes–Consani the relevant quantity is the smallest eigenvalue on a window, which is astronomically small. In (A) it is the sequence of pivots in a fixed order, which stays ≥ 1.249·d_1 under RH even though λ_min(G_N) → 0. Pivots dominate λ_min, not conversely, so the two regimes are compatible.
- **Integrality.** CCM's Z[1/√2] result concerns the coefficients of orthogonal polynomials for a single local factor. It is not a lattice minimum statement.

### Gaps
- Not examined beyond the abstracts used in the earlier note:
  - Connes–Consani's Riemann–Roch for Spec ℤ papers;
  - the scaling-site papers (beyond the 2026 survey's description);
  - "Weil positivity and trace formula" sequels for S-semilocal forms with primes.
- I found no Connes–Consani statement about Gram–Schmidt pivots of translates of a fixed test function.

## Q4. RH equivalents phrased via Gram matrices, pivots, Cholesky factors, successive minima, shortest vectors or lattices; Gram matrices indexed by integers or rationals with entries depending on m/n

### Takeaway
Two families of prior art sit close to the positive-semidefinite (PSD) layer of the orbit criterion, and none to (A) or (B).

**The function itself has been studied.** K_H(X) = Σ_ρ X^{ρ−1/2}/(ρ(1−ρ)):
- is Matsumoto–Suzuki's H_1(X);
- equals, under RH, Nicolas's W(x).

Matsumoto–Suzuki prove: **RH ⟺ H_1(e^t) − H_1(1) is a Kreĭn screw function on ℝ**. That is a positive-semidefiniteness statement for all finite point configurations, of the same kind as "G_N ⪰ 0 for all N" (they work with the screw kernel rather than K_H itself). Nicolas uses |W(x)| ≤ β = K_H(1) and lim sup W = β under RH.

**Suzuki's screw-function criteria.** Suzuki 2023 gives RH-equivalents by:
- PSD of the screw kernel of the prime function Ψ;
- pointwise nonnegativity of Ψ;
- nonnegativity of Hankel determinants of the moments of Ψ, the only determinant/pivot-sign RH criterion found.

**What was not found:**
- an RH criterion with pivots bounded below by the first pivot;
- any formulation via shortest vectors, successive minima or integer lattices.

Lattice reduction appears with zeta zeros only as a computational tool (Odlyzko–te Riele, Best–Trudgian).

### Cited Findings
- **Matsumoto–Suzuki: the same function as K_H** (full text v2) — [arXiv:2409.00888; J. Number Theory 280 (2026) 918–946, zbMATH 1584.11087](https://arxiv.org/abs/2409.00888).
  - **Definition (1.5).** "H_1(X) := Σ_ρ X^{ρ−1/2}/(ρ(1−ρ)), X ≥ 1", introduced as a variant of Fujii's H(X) = Σ X^{ρ−1/2}/(ρ(ρ+1)).
  - **Where it occurs.** It governs the Goldbach-type asymptotic Σ_{n≤X} n^{−2} Σ_{m+k=n}Λ(m)Λ(k) = log X + c_2 + (2/√X)H_1(X) + E(X) (1.6). It also governs Nicolas's lim sup for the Euler function.
  - **Krein–Langer definition of a screw function.** g is a screw function on ℝ if g(−t) = conj g(t) and G_g(t, u) := g(t − u) − g(t) − g(−u) + g(0) "is nonnegative definite on ℝ×ℝ, that is, Σ_{i,j} G_g(t_i, t_j)ξ_i ξ̄_j ≥ 0 for any n, t_i ∈ ℝ, ξ_i ∈ ℂ".
  - **Theorem 1.3.** "The function g_{H_1}(t) := H_1(e^t) − H_1(1) is a screw function on ℝ if and only if the Riemann hypothesis holds." It is a special case of Cor. 4.1. They add: "It shows a remarkable property of H_1(X) that H(X) does not have."
  - **Corollary 3.1 (general).** For f_Π(t) = Σ_{ω∈Ω} a(ω)e^{−itω} with Σ|a(ω)| < ∞, |Im ω| bounded and Ω closed under conjugation, Re(f_Π(t) − f_Π(0)) is bounded on [0, ∞) iff Ω ⊂ ℝ.
  - **Under RH plus linear independence of the ordinates** (Thm 1.4), H_1 has an M-function; exp(y·g_{H_1}) is the characteristic function of an infinitely divisible law.
- **Nicolas: the same function and the same constant** (full text) — [Nicolas, "Small values of the Euler function and the Riemann hypothesis", arXiv:1202.0729; Acta Arith. 155 (2012) 311–321](https://arxiv.org/abs/1202.0729).
  - **(1.3)** β = Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log π − 2 log 2 = 0.0461914179…
  - **(1.18)–(1.19)** W(x) = Σ_ρ x^{i Im ρ}/(ρ(1−ρ)), and "under RH … |W(x)| ≤ β".
  - **§4.** "By the pigeonhole principle … one can show that lim sup_{x→∞} W(x) = β".
  - **Theorem 1.1.** Under RH, lim sup c(n) = e^γ(2 + β) = 3.6444150964…, where c(n) = (n/φ(n) − e^γ log log n)√(log n). If RH fails, c(N_k) is unbounded above and below.
- **Suzuki 2023: screw-function equivalents of RH** (full text) — [arXiv:2206.03682; J. London Math. Soc. 108 (2023) 1448–1487](https://arxiv.org/abs/2206.03682).
  - **(1.1)** Ψ(t) := 4(e^{t/2} + e^{−t/2} − 2) − Σ_{n≤e^t} Λ(n)n^{−1/2}(t − log n) + (t/2)(Γ′/Γ(1/4) − log π) + ¼(C − e^{−t/2}Φ(e^{−2t}, 2, 1/4)). Unconditionally Ψ(t) = Σ_γ (1 − cos γt)/γ² (Thm 1.1).
  - **Theorem 1.2.** "The RH is true if and only if g(t) defined by (1.8) [g = −Ψ] is a screw function on ℝ." Under RH the kernel is G_g(t, u) = Σ_γ (e^{iγt} − 1)(e^{−iγu} − 1)/γ² (1.9).
  - **Theorem 1.3 (Weil-type).** RH ⟺ ⟨φ, φ⟩_{G_g,a} ≥ 0 on C_0(a) for every a. Under RH the form is positive definite on L²(−a, a).
  - **Theorem 1.4 (Yoshida-type).** RH ⟺ the form is non-degenerate on L²(−a, a) for every a.
  - **Theorem 1.6.** RH ⟺ Ψ(t) = O(1).
  - **Theorem 1.7.** "The RH is true if and only if Ψ(t) is pointwise non-negative", i.e. the diagonal G_g(t, t) = 2Ψ(t) ≥ 0.
  - **Theorem 1.8.** With µ_n = ∫_0^∞ 4^{−1}e^{−t/2}Ψ(t)tⁿdt and Hankel matrices Δ_n = (µ_{i+j}), Δ_n^{(1)} = (µ_{i+j+1}), "the RH is true if and only if det Δ_n ≥ 0 and det Δ_n^{(1)} ≥ 0 for all n".
  - **Theorems 4.1–4.2 (unconditional).** Ψ(t) > 0 on (0, t_0) with t_0 > log 2; G_g is positive definite on L²(−a, a) for small a.
- **Multiplicative Toeplitz matrices (entries depending on i/j).**
  - **Hilberdink 2006.** "The author refers to the matrices (c(i/j))_{i,j≥1} as multiplicative Toeplitz matrices". The associated series is Σ_q c(q)q^{it} over positive rationals. For c multiplicative on ℚ₊, the determinants of truncations factor as Euler products. Source: [Hilberdink, Acta Arith. 125 (2006) 265–284, zbMATH 1153.11014 review](https://zbmath.org/?q=an:1153.11014).
  - **Hilberdink 2015.** "Multiplicative Toeplitz matrices and the Riemann zeta function", Four Faces of Number Theory, EMS (2015) 77–121; title only, no review — [zbMATH 1382.11055](https://zbmath.org/?q=an:1382.11055).
  - **Nikolski–Pushnitski 2021.** An analogue of the first Szegő limit theorem for multiplicative Toeplitz operators, "relating the spectral asymptotics of large truncated multiplicative Toeplitz matrices to the values of the symbol" — [St. Petersburg Math. J. 32 (2021) 1033–1050, zbMATH 1512.47055 review](https://zbmath.org/?q=an:1512.47055).
  - **Hilberdink–Pushnitski 2023.** Spectral asymptotics λ_n(E) = κn^{−ρ} + o(n^{−ρ}) for the LCM matrices (n^σ m^σ/[n,m]^τ) — [zbMATH 1530.47036](https://zbmath.org/?q=an:1530.47036).
- **Lattice reduction applied to zeta zeros: tools, not criteria.**
  - **Odlyzko–te Riele.** They disprove Mertens via "the lattice basis reduction algorithm of Lenstra, Lenstra, and Lovasz", applied after computing zeros "to about 100 significant decimal digits". "The disproof relies on extensive computations with the zeros of the zeta function, and does not provide an explicit counterexample." Source: [Odlyzko–te Riele, CWI report NM-R8412 (1984), full text; J. reine angew. Math. 357 (1985) 138–160](https://ir.cwi.nl/pub/6447/6447D.pdf).
  - **Best–Trudgian.** They study "linear relations between the non-trivial zeroes" and obtain lim sup M(x)x^{−1/2} ≥ 1.6383 — [arXiv:1209.3843; Math. Comp. 84 (2015) 2433–2446](https://arxiv.org/abs/1209.3843).
- **Searches for "shortest vector" or "lattice" with RH returned no criteria.**
  - zbMATH queries returned only lattice-cryptography papers in which RH or GRH is an *assumption*, e.g. Düzlü–Krämer, "Application of automorphic forms to lattice problems", J. Math. Cryptol. 16 (2022) — [zbMATH 1491.14042](https://zbmath.org/?q=an:1491.14042).
  - A web hit, IACR ePrint 2024/1714, is a speculative, non-peer-reviewed preprint on quantum-gravity algorithms for SVP that mentions RH only loosely, with no theorem — [ePrint 2024/1714](https://eprint.iacr.org/2024/1714).
- **Nyman–Beurling Gram matrices**, the other family of number-theoretic Gram matrices with integer-indexed homogeneous entries. Dimitrov–Oliveira give the Gram-determinant ratio for d_n², and Alouges–Darses–Hillion obtain a "block Hankel" second Gram matrix ([JTNB 34 (2022) 767–785](https://doi.org/10.5802/jtnb.1227)). No pivot lower bounds; see the earlier note, Q1 and Q3.

### Inferences
- **The PSD layer is a discretisation of known results.** K_H = H_1, and H_1(e^{t−u}) is the kernel whose Gram matrices at t_i = log n_i, rescaled by √(mn), are G_N. So "RH ⟺ G_N ⪰ 0 for all N" discretises Matsumoto–Suzuki's Theorem 1.3 at the points log n. It is slightly stronger as a hypothesis: positive definiteness of K_H rather than of its screw kernel. Its proof idea, that PSD forces boundedness and boundedness forces RH, is Matsumoto–Suzuki's Cor. 3.1 and Suzuki's Thm 1.6.
- **2×2 minors already suffice (derived here).**
  - The 2×2 principal minor of G_N at (m, n) is mn(K_H(1)² − K_H(m/n)²).
  - Nonnegativity of all of them is |K_H(r)| ≤ K_H(1) on the dense set ℚ₊, hence on ℝ₊.
  - By Matsumoto–Suzuki Cor. 3.1, boundedness implies RH.
  - So RH ⟺ every 2×2 principal minor of every G_N is ≥ 0. This is the matrix form of Nicolas's |W| ≤ β.
- **A Diophantine reading of (A) (derived here).** d_k ≤ dist²(w_k, ℝw_1) = k(K_H(1)² − K_H(k)²)/K_H(1). So d_k ≥ 1.249·d_1 implies, under RH, |K_H(k)| ≤ K_H(1)(1 − 0.624/k) for every integer k ≥ 2.
  - Compare Nicolas's lim sup_{x→∞} W(x) = β over real x.
  - The pivot theorem quantifies how slowly integer points can approach that supremum.
  - This uses 0.0577/0.04619 = 1.2491 (computed here).
- **(A) as a ratio of multiplicative Toeplitz determinants (derived here).** With T_k = (K_H(m/n))_{m,n≤k}, G_k = D^{1/2}T_kD^{1/2} with D = diag(1, …, k), so det G_k = k!·det T_k and d_k = k·det T_k/det T_{k−1}.
  - (A) is therefore a lower bound det T_k/det T_{k−1} ≥ K_H(1)/k, a Szegő–Kolmogorov-type one-step prediction-error bound for multiplicative Toeplitz matrices with the discrete symbol Σ_ρ δ_γ/|ρ|².
  - Hilberdink's Euler-product factorisation does not apply, since K_H is not multiplicative on ℚ₊.
  - Nikolski–Pushnitski's Szegő analogue concerns eigenvalue distributions, not determinant ratios.
  - I found no determinant-ratio (second Szegő theorem) result for multiplicative Toeplitz matrices with singular symbols.
- **Suzuki's Hankel criterion compared with (A).** Theorem 1.8 is the only RH criterion found stated via Gram-type determinants. It amounts to "all leading pivots of the moment Hankel matrices of Ψ are ≥ 0" (Hankel = Gram of monomials), a Sylvester-type sign condition. (A) differs in three ways:
  - the vectors are multiplicative translates, not monomials;
  - the threshold is d_1, not 0;
  - its equivalence with RH is not formal, because the RH ⇒ (A) direction needs the explicit-formula estimate.
- **(B) follows from (A).** Under RH, (B) follows from (A) by the standard lattice fact that a nonzero integer vector with last nonzero index k has norm² ≥ d_k; uniqueness up to sign uses d_k > d_1 for k ≥ 2. For ¬RH ⇒ ¬(B), an indefinite G_N gives a rational, hence integer, vector with Q_N < 0. I found no RH criterion in the literature of this integrality type (integer Dirichlet polynomials Σ a_n n^s with a ∈ ℤ^N).

### Gaps
- Not read: Hilberdink's 2015 chapter (title only), and Nikolski–Pushnitski beyond the review. They might contain determinant-ratio results.
- MathSciNet was not accessible. The zbMATH API queries "Riemann hypothesis Gram-Schmidt", "…Cholesky" and "…Gram matrix positive definite" failed, returning server errors; the hyphenated forms could not be retried in other phrasings within budget.

## Q5. Arakelov viewpoint: Stuhler–Grayson filtrations, Bost's slopes and theta invariants, Euclidean lattices attached to ζ; is semistability of an arithmetic lattice related to RH?

### Takeaway
The Euclidean-lattice side of Arakelov geometry offers the right vocabulary:
- slopes, the canonical (Stuhler–Grayson) filtration and semistability;
- Bost's 1997 tensor-product conjecture;
- theta invariants h⁰_θ and successive minima.

I found no source relating the slopes, minima or semistability of a lattice built from ζ's zeros or from the explicit formula to RH for ζ. The one place where semistable lattices and a Riemann hypothesis meet is Weng's non-abelian zeta functions. These are integrals over moduli of semistable lattices, with rank 1 recovering ζ̂. RH is proved for some of them (rank 2 over ℚ; Chevalley-group versions; genus-1 curves), but that RH concerns those new zeta functions, not ζ.

### Cited Findings
- **Stuhler, Grayson, Bost (via Coulangeon).** "The slope filtration of Euclidean lattices was introduced in works by Stuhler in the late 1970s, extended by Grayson a few years later, as a new tool for reduction theory… Lattices with trivial filtration are called semistable… In 1997, Bost conjectured that the tensor product of semistable lattices should be semistable itself." Source: [Coulangeon, "On slopes of isodual lattices", arXiv:2206.00331 (2022), abstract](https://arxiv.org/abs/2206.00331).
- **Coulangeon–Nebe.** "A general conjecture predicts that µ_min(L ⊗ M) = µ_min(L)µ_min(M)", proved under multiplicity-free group actions — [arXiv:1806.04984, abstract](https://arxiv.org/abs/1806.04984).
- **Bost's theta invariants.** h⁰_θ(Ē) := log Σ_{v∈E} e^{−π‖v‖²}. These invariants "naturally arise when one investigates basic questions concerning classical invariants of Euclidean lattices, such as their successive minima, their covering radius" — [Bost, "Euclidean lattices, theta invariants, and thermodynamic formalism", arXiv:1909.04992 (2019), abstract](https://arxiv.org/abs/1909.04992).
- **Weng's non-abelian zeta functions.**
  - **Weng 2019.** "Over the moduli space of rank n semi-stable lattices is a universal family of tori… rank n non-abelian zeta functions of the field of rationals, which are known [to] lie on the central line except a finitely many if n ≥ 2"; for n = 1 the construction recovers the classical case — [Weng, arXiv:1903.03604 (2019), abstract](https://arxiv.org/abs/1903.03604).
  - **Lagarias–Suzuki.** "For T = 1 this proves the Riemann hypothesis for a zeta function recently introduced by Lin Weng, attached to rank 2 semistable lattices over the rationals" — [Lagarias–Suzuki, arXiv:math/0412039; J. Number Theory 118 (2006) 98–122](https://arxiv.org/abs/math/0412039).
  - **Ki–Komori–Suzuki.** "On the zeros of Weng zeta functions for Chevalley groups", Manuscr. Math. 148 (2015) 119–176 (title and data only) — [zbMATH 1391.11102](https://zbmath.org/?q=an:1391.11102).
  - **Weng–Zagier, function fields.** RH for Weng's higher-rank zeta functions of genus-1 curves (PNAS 117 (2020) 4546–4558), and the identification of the rank-n zeta function with the SL_n-period zeta function (PNAS 117 (2020) 6398–6408) — [zbMATH 1473.11172](https://zbmath.org/?q=an:1473.11172), [zbMATH 1473.11173](https://zbmath.org/?q=an:1473.11173).

### Inferences
- **Translation into slope language (derived here; conventions deg Ē = −log covol, µ = deg/rank).**
  - Let L_k = ℤw_1 + … + ℤw_k. The k-th subquotient of the orbit flag has slope µ(L_k/L_{k−1}) = −½ log d_k.
  - (A) says every subquotient slope is ≤ µ(L_1) = −½ log K_H(1). Under RH it is ≤ µ(L_1) − ½ log 1.249 for k ≥ 2.
  - Then µ(L_1) > µ(L_N) for N ≥ 2, so **each orbit lattice L_N is unstable, destabilised by ℤw_1**. Under RH, w_1 spans the first minimum, which is (B) phrased via −log λ_1(L_N) = µ(ℤw_1).
  - Equivalently: RH ⟺ "the first step of the orbit flag is the most stable piece, in a flag whose later steps never exceed it".
- **Coverage.** No Arakelov-theoretic source checked here uses a flag of translates of a test function, or the explicit formula as a metric. Weng's construction integrates over all semistable lattices; it does not study one distinguished lattice built from ζ.

### Gaps
- Bost's monograph and lecture notes were seen only through abstracts. Grayson's and Stuhler's original papers were not consulted. Van der Geer–Schoof (effectivity of Arakelov divisors) and Connes–Consani's "Riemann–Roch for Spec ℤ" were not checked for RH-related slope statements.

## Q6. Function-field analogue: Weil's proof via Castelnuovo–Severi and Hodge index as Gram matrices of the Frobenius orbit; is it phrased via pivots or shortest vectors, and do pivot margins fail for curves?

### Takeaway
There is a published precise analogue of the orbit Gram matrix: Hallouin–Perret, TAMS 2019 (arXiv 2014).
- **Set-up.** In the Euclidean space E_X = (Hodge-index-negative part of NS(X × X), −intersection), the classes Γ^k of the graphs of the Frobenius powers F^k have a Gram matrix that, after normalisation, is a symmetric Toeplitz matrix in the point counts.
- **Bounds from Gram determinants.** Weil's bound is the 2×2 Gram determinant of (Γ^0, Γ^1). Ihara's bound is the 3×3 one, and they push to all orders.
- **Finite rank.** The span of the Γ^k has dimension equal to the degree of the minimal polynomial of Frobenius, at most 2g.

Connes–Consani explicitly model their Toeplitz analysis of the archimedean Weil form on this technique. No source phrases the curve case through pivot lower bounds or shortest vectors. The structure shows that the analogue of (A) **fails for curves**: pivots vanish beyond the rank, and already the second pivot vanishes for Weil-maximal or Weil-minimal curves.

### Cited Findings
- **Hallouin–Perret** (full text of the arXiv version) — [arXiv:1409.2357 (2014)](https://arxiv.org/abs/1409.2357); published as "A unified viewpoint for upper bounds for the number of points of curves over finite fields via Euclidean geometry and semi-definite symmetric Toeplitz matrices", [Trans. Amer. Math. Soc. 372 (2019), no. 8, 5409–5451, doi:10.1090/tran/7813](https://doi.org/10.1090/tran/7813) (Crossref-verified; the TAMS version itself was not read).
  - **Approach.** "We push further the classical proof of Weil upper bound … in term of euclidean relationships between the Neron Severi classes in X × X of the graphs of iterations of the Frobenius morphism."
  - **Euclidean structure.** "The intersection pairing on the Neron Severi space NS(X × X)_ℝ is anti-euclidean on the orthogonal complement E_X of the trivial plane generated by the horizontal and vertical classes."
  - **Lemma 3.** ⟨p(Γ^k), p(Γ^k)⟩ = 2gq^k, and ⟨p(Γ^k), p(Γ^{k+i})⟩ = q^k((q^i + 1) − #X(F_{q^i})), where p is the projection to E_X and Γ^k the class of the graph of F^k.
  - **Weil's bound as a 2×2 Gram determinant.** "0 ≤ Gram(p(Γ^0), p(Γ^1)) = (2g√q)² − (q + 1 − #X(F_q))² is nothing else than Weil inequality."
  - **Normalised Gram matrix (Definition 4, (5)).** With γ_k = p(Γ^k)/√(2gq^k) and x_i = ((q^i + 1) − #X(F_{q^i}))/(2g q^{i/2}), the Gram matrix of γ_0, …, γ_n is the symmetric normalised Toeplitz matrix with first row (1, x_1, …, x_n). "X is Weil-maximal if and only if x_1 = −1, and is Weil minimal if and only if x_1 = 1."
  - **Higher orders.** "Cauchy–Schwartz between two vectors is the non-negativity of their 2 × 2 Gram determinant. Hence, we are cheered on investigating the consequences of the non-negativity of larger Gram determinants". Γ^0, Γ^1, Γ^2 recover Ihara's bound, a "second order Weil bound". Γ^0, …, Γ^3 give a new third-order bound (Theorem 18). "Non-negativity of the Gram determinants of any orders" gives Theorem 22, a refinement of Tsfasman's bound.
  - **Comparison with Oesterlé.** Their algorithmic higher-order bounds always reproduced the Oesterlé bounds numerically, which they "were not … able to understand".
  - **Remark after Lemma 3, rank.** "We are working along this article only on the subspace F of E generated by the family p(Γ^k), k ≥ 0… for a given curve X over F_q of genus g, we actually are working in an euclidean space F_X of dimension equal to the degree of the minimal polynomial of φ_ℓ on V_ℓ(Jac X)." This rests on Mumford's appendix in Zarhin's book.
- **Connes–Consani tie their method to Hallouin–Perret.** "The method used in 2. and 3. [Toeplitz discretisation and canonical form] is closely related to the technique applied in [21] in the context of RH for curves over finite fields", with [21] the TAMS paper — [Connes–Consani 2021, full text](https://arxiv.org/abs/2006.13771).
- **Bombieri's dictionary.** He calls the Weil functional T "an analogue of Weil's definition of trace of a correspondence" and τ_a "the analogue of a normalized Frobenius operator" — [Bombieri 2000, full text](http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0).
- **Connes 2026 on Weil's proof.** Weil's proof "used the intersection pairing on divisors and the Hodge index theorem". For ℚ, "the Frobenius correspondences make sense on the square of the scaling site and the completed Riemann zeta function appears as the analogue of the Hasse–Weil generating function" — [Connes 2026, full text](https://arxiv.org/abs/2602.04022).

### Inferences
- **The dictionary (derived here).**
  - Γ^k = (F^k × id)^*Δ, the orbit of the diagonal under Frobenius, corresponds to w_n, the orbit of w_1 under the scaling τ_n.
  - The norm 2gq^k corresponds to n·K_H(1); q^k corresponds to n.
  - Under Weil's theorem (|α_j| = √q), ⟨p(Γ^k), p(Γ^l)⟩ = Σ_j ᾱ_j^k α_j^l. This parallels G_N(m, n) = Σ_ρ m^ρ n^{ρ̄}/|ρ|² under RH.
  - So the function-field "K_H" is r = q^i ↦ Σ_j (α_j/√q)^i, with unit weights on finitely many eigenvalues instead of weights 1/|ρ|² on infinitely many zeros.
- **The analogue of (A) fails for curves.**
  - The Gram matrix of γ_0, …, γ_n has rank equal to deg(minimal polynomial of Frobenius) ≤ 2g, so every Gram–Schmidt pivot beyond that index is 0 < d_1.
  - For a Weil-maximal or Weil-minimal curve, x_1 = ±1, so the second pivot is already 1 − x_1² = 0.
  - More generally d_2 ≥ d_1 is equivalent to |q + 1 − #X(F_q)| ≤ 2g√(q − 1) (unnormalised d_1 = 2g, d_2 = 2gq(1 − x_1²)), a strict strengthening of Weil's bound that fails for curves near the bound.
  - Pivot margins are therefore a genuinely number-field phenomenon. (A) needs infinitely many zeros, under RH all w_n are independent, and the decaying weights 1/|ρ|².
- **The analogue of (B) holds when the Weil polynomial is irreducible (derived here, not found in any source).**
  - For P = Σ a_k x^k ∈ ℤ[x], ‖Σ a_k p(Γ^k)‖² = Σ_{j=1}^{2g} |P(α_j)|². By AM–GM this is ≥ 2g·|Π_j P(α_j)|^{1/g}.
  - Π_j P(α_j) is a resultant with the monic integral reversed L-polynomial, hence a nonzero integer whenever P(α_j) ≠ 0 for all j.
  - If the Weil polynomial is irreducible, every nonzero lattice vector has that property. So the diagonal class p(Δ), of norm² 2g, is a shortest vector of the Frobenius-orbit lattice, by integrality alone.
  - For reducible Weil polynomials the argument only bounds each Galois orbit separately. I did not settle whether counterexamples to the analogue of (B) exist.
  - In the curve case, (B)'s analogue is thus an arithmetic (norm) phenomenon, while (A)'s analogue is false.

### Gaps
- The TAMS 2019 version (title changed to stress "semi-definite symmetric Toeplitz matrices") was not read. It may contain additional statements, for example on Gram–Schmidt or Cholesky structure of the Toeplitz matrices.
- No source was found that discusses Gram–Schmidt pivots, Cholesky factors, successive minima or shortest vectors for the Frobenius-orbit lattice in NS(X × X), or for the Rosati-positive lattice End(Jac X).

## Q7. Verdict: is (A) or (B), or a close variant, in the literature?

### Takeaway
**(A), RH via Gram–Schmidt pivots of the orbit vectors bounded below by the first pivot, was not found in any source examined. Neither was (B), RH via w_1 being the (unique up to sign) shortest vector of the integer orbit lattice. No RH-equivalent phrased through lattices, shortest vectors or successive minima was found at all.**

What is in the literature are the surrounding layers:
- **The function K_H itself and the PSD-type equivalence.** Matsumoto–Suzuki's H_1 = K_H with "RH ⟺ H_1(e^t) − H_1(1) is a screw function". Nicolas's W(x) with |W| ≤ β = K_H(1) and lim sup W = β under RH. Suzuki's screw-function and Hankel-determinant criteria.
- **Finite-dimensional sign counting on the zero side.** Bombieri's Theorem 8.
- **Margins only on windows or high modes.** Yoshida's Lemma 3; Bombieri's Theorem 12.
- **The function-field Gram matrix of the Frobenius orbit.** Hallouin–Perret, where Gram determinants of all orders give point-count bounds, but where the analogue of (A) provably fails because of finite rank.

### Cited Findings
- **Closest results, ranked by how much of the structure of (A)/(B) they share:**
  1. **Matsumoto–Suzuki, Thm 1.3.** Same function: H_1(X) = Σ_ρ X^{ρ−1/2}/(ρ(1−ρ)) = K_H. RH ⟺ the kernel H_1(e^{t−u}) − H_1(e^t) − H_1(e^{−u}) + H_1(1) is PSD on every finite point set. A PSD criterion only: no pivots, no margin, no lattice. [arXiv:2409.00888; JNT 280 (2026)](https://arxiv.org/abs/2409.00888).
  2. **Nicolas.** Same function and same constant: W(x) = Σ x^{i Im ρ}/(ρ(1−ρ)), |W(x)| ≤ β = 2 + γ − log 4π under RH, lim sup W = β. These are the 1×1 and 2×2 consequences, not pivots. [arXiv:1202.0729](https://arxiv.org/abs/1202.0729).
  3. **Hallouin–Perret.** Gram matrices of an orbit (graphs of Frobenius powers) in a Euclidean space attached to the curve. Weil, Ihara and higher bounds come from Gram determinants; the span has finite rank. [arXiv:1409.2357; TAMS 372 (2019)](https://doi.org/10.1090/tran/7813).
  4. **Bombieri 2000, Theorem 8 and Lemma 10.** Inertia of finite truncations H(Γ; t) indexed by zeros: negative eigenvalues ↔ off-line conjugate pairs; no zero eigenvalue for simple zeros. [BDIM](http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0).
  5. **Suzuki 2023, Thms 1.2, 1.7, 1.8.** RH ⟺ PSD of a prime-built screw kernel ⟺ Ψ ≥ 0 ⟺ Hankel determinants of moments ≥ 0. This is the only determinant/pivot-sign criterion found. [arXiv:2206.03682](https://arxiv.org/abs/2206.03682).
  6. **Yoshida 1992, Lemmas 2–3 (as restated by Suzuki) and Bombieri 2000, Theorem 12.** Quantitative positivity margins, but only on small windows or high Fourier modes. [Suzuki](https://arxiv.org/abs/2206.03682); [Bombieri](http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0).
  7. **Connes–Consani 2021/2023, CCM 2024.** Toeplitz discretisations on q^ℤ, Gram–Schmidt of prolate vectors and Hankel/Jacobi (Aitken–Cholesky) structures, all as computational devices on windows. [arXiv:2006.13771](https://arxiv.org/abs/2006.13771); [arXiv:2106.01715](https://arxiv.org/abs/2106.01715); [arXiv:2403.01247](https://arxiv.org/abs/2403.01247).
- **Lattice methods with zeta zeros** (Odlyzko–te Riele; Best–Trudgian) are LLL computations for Mertens-type questions, not RH criteria. [CWI report](https://ir.cwi.nl/pub/6447/6447D.pdf); [arXiv:1209.3843](https://arxiv.org/abs/1209.3843).

### Inferences
- **What is new (relative to everything found).**
  - (A) puts a *uniform positive margin*, the ratio 1.249 relative to the first pivot, on the *Gram–Schmidt pivots of a natural ordered family* (the multiplicative translates of 1_{(0,1]}). It is proved under RH from the explicit formula.
  - It is not a spectral statement, since λ_min(G_N) → 0. It has no window restriction.
  - (B) is the first integrality formulation: integer step functions Σ a_n 1_{(0,n]}, equivalently integer Dirichlet polynomials.
  - The "⇐" directions of both are formal once PSD ⟺ RH is in hand, and that layer has close precedent in Matsumoto–Suzuki and Nicolas. The "⇒" content, the margin, is the novel part.
- **Suggested positioning in the write-up.**
  - Cite Matsumoto–Suzuki Thm 1.3 and Nicolas (1.18)–(1.19) for K_H and the PSD layer.
  - Cite Bombieri 2000 Thm 8 as the nearest finite-dimensional sign-count result.
  - Cite Hallouin–Perret, with Connes–Consani's remark, for the function-field Gram/Toeplitz analogue, noting that there the pivot margin fails (rank ≤ 2g; d_2 = 0 for maximal curves) while the shortest-vector analogue follows from integrality when the Weil polynomial is irreducible.
  - Present (A) and (B) as new.
- **A by-product worth stating.** Under RH, |K_H(k)| ≤ K_H(1)(1 − 0.624/k) for every integer k ≥ 2, a quantitative counterpart, at integer points, of Nicolas's lim sup W = β.

### Gaps
- **Coverage limits.** MathSciNet was not accessible. zbMATH was queried through its API (several hyphenated queries failed). Searches covered arXiv metadata and full texts, and web search.
- **Primary sources not read:**
  - Yoshida 1992 (Project Euclid blocked);
  - Bombieri 2003 (Wiley blocked);
  - Hilberdink 2015;
  - the TAMS version of Hallouin–Perret;
  - Broughan's *Equivalents of the Riemann Hypothesis* (Cambridge 2017), the most likely place for a catalogued Gram/lattice criterion. Not checked; it should be checked before claiming absolute novelty.
- **Surveys not consulted** beyond Connes 2026: Conrey's Notices survey, Bombieri's Clay description and Lagarias's talks.
