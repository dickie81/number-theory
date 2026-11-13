# Prior art for the orbit-lattice Gram matrix G_N = (√(mn)·K_H(m/n)): multiplicative Toeplitz matrices, Weil-type Gram matrices, pivots and lattices

**Scope.** The object is G_N = (√(mn)·K_H(m/n))_{m,n≤N} with K_H(r) = Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)). Equivalently, its (m, n) entry is Σ_ρ m^ρ n^{1−ρ}/(ρ(1−ρ)), computable from Chebyshev's ψ by the explicit formula, and K_H(1) = 2 + γ − log 4π.

The repository's claims under check are:
- under RH, √(log N)/N ≪ λ_min(G_N) ≪ log N/N, with the conjecture λ_min ∼ 0.0429·log N/N;
- under RH, the Gram–Schmidt (Cholesky) pivots satisfy d_k ≥ 0.0577 for k ≥ 2, d_k ≫ log k, and d_k ≤ log(k/2π) + 1 − γ + o(1);
- RH ⟺ d_k ≥ d_1 for all k;
- RH ⟺ e_1 is a shortest nonzero integer vector of G_N for every N;
- the flat model: with Lebesgue measure in place of the zeros, G_N becomes min(m, n).

**Not redone here.** The earlier notes ([gram_and_nyman_beurling.md](../Sampling%20Dirichlet%20polynomials%20at%20zeta%20zeros/gram_and_nyman_beurling.md) and the [report](../../reports/Sampling%20Dirichlet%20polynomials%20at%20zeta%20zeros.md)) already cover:
- Nyman–Beurling lower and upper bounds;
- Weil windows (Yoshida, Connes–Consani, Zhu, Suzuki);
- Li's criterion;
- the Landau–Gonek and Montgomery–Odlyzko discrete mean values.

They are cited below only where needed.

**Source tags:**
- "full text": I read the PDF this session.
- "abstract": abstract only.
- "snippet": search-engine summary only.
- "title only": bibliographic record verified (Crossref or arXiv), content not read.

Statements marked "(computed here)" are my own derivations, not taken from a source.

## Q1. Multiplicative Toeplitz matrices (a(m/n)) and (a(mn)): do Hilberdink, Brevig–Perfekt–Seip–Siskakis–Vukotić, Bondarenko–Seip and Aistleitner–Berkes–Seip use kernels built from the zeta zeros, and is positivity ever equivalent to RH?

### Takeaway
No. The multiplicative Toeplitz literature uses symbols built from ζ itself, or from Dirichlet series with arithmetic coefficients, never from the zeros.

Positivity of its matrices is always unconditional: they are Gram matrices of dilated functions, or have non-negative symbols. RH enters only through growth questions:
- Redheffer's determinant;
- norms tied to max |ζ(σ+it)|.

The structure √(mn)·K(m/n) is shared by Smith's GCD matrix (gcd(m,n)), which is the s = 1/2 member of the Lindqvist–Seip family. That family is the closest prior object, and it carries a sharp smallest-eigenvalue theorem.

### Cited Findings
- **Hilberdink, "Multiplicative Toeplitz matrices and the Riemann zeta function"** (chapter in *Four Faces of Number Theory*, EMS 2015, pp. 77–122) — [accepted manuscript, full text](https://centaur.reading.ac.uk/50981/).
  - **Definition.** Matrices with entries f(i/j), f a function on ℚ₊, with formal symbol Σ_{q∈ℚ₊} f(q)q^{it}. For f(n) = n^{−α} supported on ℕ the symbol is ζ(α ∓ it); the sign is garbled in my text extraction.
  - **Novelty remark.** Hilberdink writes: "Rather surprisingly perhaps, these type of matrices do not appear to have been studied much at all – at least not in this respect."
  - **Thm 2.1 (boundedness).** For f ∈ ℓ¹(ℚ₊), the map (a_n) ↦ (Σ_m f(n/m)a_m) is bounded on ℓ² with norm sup_t |Σ_q f(q)q^{it}| = ‖F‖_∞.
  - **Thm 2.4 (invertibility, Wiener–Hopf analogue).** For factorisable f, M(f) is invertible iff w(f) = 0. Here w is a mean-motion index, with w(f) = log q for the factor q.
  - **Thm 3.1 (norms of convolution by n^{−α}).** Let Φ_α(N) be the norm of the N-truncated Dirichlet convolution by n^{−α}, b_n = Σ_{d|n} d^{−α}a_{n/d}. Then:
    - Φ_1(N) = e^γ log log N + O(1);
    - log Φ_α(N) ≍ (log N)^{1−α}/log log N for 1/2 < α < 1;
    - log Φ_{1/2}(N) ≍ (log N/log log N)^{1/2}.

    The constants are read from a garbled PDF extraction. These parallel max_{|t|≤T} |ζ(σ+it)|; the chapter quotes Z_1(T) ≲ 2e^γ log log T on RH.
  - **Cor. 4.1–4.2 (largest eigenvalues).** These give the largest eigenvalue Λ_N of (f(ij/(i,j)²))_{i,j≤N}. For f(n) = n^{−1}, Λ_N(1) = (6/π²)(e^γ log log N + O(1))².
  - **RH appears in two ways only.** First, through Redheffer's matrix: det R_n = M(n), so "RH holds if and only if det R_n = O(n^{1/2+ε})". Second, through the Lindelöf hypothesis. No symbol is built from zeros.
- **Hilberdink's earlier papers.** The chapter credits the 2006 paper with the Euler-product factorisation M(f) = Π_p M(f_p) for multiplicative f — [chapter](https://centaur.reading.ac.uk/50981/). Bibliographic records (title only, content beyond the chapter not read):
  - Hilberdink, "Determinants of multiplicative Toeplitz matrices", *Acta Arith.* 125 (2006) 265–284 — [DOI](https://doi.org/10.4064/aa125-3-4).
  - Hilberdink, "An arithmetical mapping and applications to Ω-results for the Riemann zeta function", *Acta Arith.* 139 (2009) 341–367 — [DOI](https://doi.org/10.4064/aa139-4-3).
  - Hilberdink, "Singular values of multiplicative Toeplitz matrices", *Linear Multilinear Algebra* 65(4) (2017) 813–829 — [DOI](https://doi.org/10.1080/03081087.2016.1204978).
- **Lindqvist–Seip, "Note on some greatest common divisor matrices"**, *Acta Arith.* 84 (1998) 149–154 — [full text](http://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8425.pdf) ([DOI](https://doi.org/10.4064/aa-84-2-149-154)).
  - **Norm identity.** With u(x) = Σ_k sin(kx)/k^s and u_n(x) = u(nx), ⟨u_m, u_n⟩_{L²(0,π)} = (π/2)ζ(2s)·gcd(m,n)^{2s}/(m^s n^s) for s > 1/2. So M_s = (gcd(m,n)^{2s}/(m^s n^s)) is a Gram matrix of dilations, hence positive definite. The same holds for S_s = (gcd(m,n)^{2s}) = (substitute c_n → n^s c_n).
  - **Breakdown at 1/2.** "Unfortunately, our characterization above of the quadratic form as a norm breaks down when s ≤ 1/2."
  - **Theorem.** Let λ_N(s) and Λ_N(s) be the smallest and largest eigenvalues of the N × N matrix M_s.
    - For s > 1: ζ(2s)/ζ(s)² ≤ λ_N(s) ≤ Λ_N(s) ≤ ζ(s)²/ζ(2s), and lim inf λ_N(s) = ζ(2s)/ζ(s)², lim sup Λ_N(s) = ζ(s)²/ζ(2s).
    - For 1/2 < s ≤ 1: lim inf λ_N(s) = 0 and lim sup Λ_N(s) = ∞.
  - **Proof.** The proof is the Riesz-basis criterion of Hedenmalm–Lindqvist–Seip (Thm 5.2), with sharp constants from the Euler product and Kronecker's theorem. "the sharp asymptotic bounds … are not attained for any finite N".
  - **Smith's determinant and factorisation.** Smith (1876) gives det(gcd(m,n))_{N×N} = φ(1)φ(2)⋯φ(N). The matrix "has been explicitly written as the product of two triangular matrices" (Smith; Bourque–Ligh, *Linear Algebra Appl.* 174 (1992) 65–74).
  - **No RH.** The Riemann hypothesis does not appear in the paper.
- **Aistleitner–Berkes–Seip, "GCD sums from Poisson integrals and systems of dilated functions"**, *JEMS* 17 (2015) 1517–1546 — [arXiv:1210.0741, abstract](https://arxiv.org/abs/1210.0741) ([DOI](https://doi.org/10.4171/jems/537)).
  - They prove upper bounds for Σ_{k,l} gcd(n_k,n_l)^{2α}/(n_k n_l)^α, 0 < α ≤ 1.
  - The method "is based on identifying the sum as a certain Poisson integral on a polydisc". As a byproduct it gives estimates for the largest eigenvalues of the associated GCD matrices.
  - No zeros appear.
- **Bondarenko–Hilberdink–Seip, "Gál-type GCD sums beyond the critical line"** — [arXiv:1512.03758, abstract](https://arxiv.org/abs/1512.03758). For 0 < α < 1/2 they prove Σ_{k,l≤N} (n_k,n_l)^{2α}/(n_k n_l)^α ≪ N^{2−2α}(log N)^{b(α)}, optimal up to b(α). Again an extremal (largest-eigenvalue) problem, with no zeros.
- **The multiplicative Hilbert matrix** (an a(mn)-type matrix, not a(m/n)):
  - **Brevig–Perfekt–Seip–Siskakis–Vukotić**, *Adv. Math.* 302 (2016) 410–432 — [arXiv:1411.7294, full text of abstract and Thm 1](https://arxiv.org/abs/1411.7294) ([DOI](https://doi.org/10.1016/j.aim.2016.07.019)).
    - The matrix (1/(√(mn) log(mn)))_{m,n≥2} is the matrix of Hf(s) = ∫_{1/2}^∞ f(w)(ζ(w+s) − 1) dw in the basis (n^{−s}).
    - Thm 1: "H is a bounded and strictly positive operator on H²_0 with ‖H‖ = π. It has no eigenvalues, and its continuous spectrum is [0, π]."
  - **Perfekt–Pushnitski**, Thm 1.1: purely absolutely continuous spectrum [0, π] of multiplicity one — [arXiv:1705.01959, full text](https://arxiv.org/abs/1705.01959) ([*Ark. Mat.* 56 (2018) 163–183](https://doi.org/10.4310/arkiv.2018.v56.n1.a10)).
  - ζ enters through ζ(w+s) − 1, not through its zeros.
- **Nikolski–Pushnitski, Szegő-type limit theorems for "multiplicative Toeplitz" operators** — [arXiv:2001.01474, full text of introduction](https://arxiv.org/abs/2001.01474) ([*St. Petersburg Math. J.* 32(6) (2021) 1033–1050](https://doi.org/10.1090/spmj/1683)).
  - A multiplicative Toeplitz operator {c(j/k)} is bounded iff c is the Fourier transform of a bounded symbol on the infinite torus 𝕋^∞.
  - For the first Szegő theorem, "the 'natural' truncation {φ̂(j/k)}_{j,k=1}^N is not admissible, i.e. it does not lead to the 'expected' asymptotic spectral density!" One must use multiplicative Følner truncations.
- **Hilberdink–Pushnitski, "Spectral asymptotics for a family of LCM matrices"** — [arXiv:2110.14323, abstract](https://arxiv.org/abs/2110.14323) ([*St. Petersburg Math. J.* 34(3) (2023) 463–481](https://doi.org/10.1090/spmj/1764)).
  - E(σ,τ) = (n^σ m^σ/[n,m]^τ) is compact and positive definite, with λ_n = κ(σ,τ)n^{−ρ} + o(n^{−ρ}).
  - Application: singular values of "truncated multiplicative Toeplitz matrices with the symbol given by the Riemann zeta function on the vertical line with abscissa σ < 1/2".
  - A sequel links such spectra to Beurling primes — [arXiv:2401.06892, abstract](https://arxiv.org/abs/2401.06892).
- **Other.**
  - Thorn studies boundedness of y_n = Σ_k f(n/k)x_k on ℓ^p — [arXiv:1801.09478, abstract](https://arxiv.org/abs/1801.09478).
  - An arXiv author listing for Hilberdink shows coauthors Pushnitski, Bondarenko, Seip, Tóth, Luca, Lapidus, Saias, Broucke and Neamah — [arXiv listing, au:Hilberdink](https://export.arxiv.org/api/query?search_query=au:Hilberdink&max_results=50).

### Inferences
- **G_N in this language (computed here).** Write D = diag(√1, …, √N).
  - Then G_N = D·(K_H(m/n))·D, a multiplicative Toeplitz matrix conjugated by D.
  - Under RH its formal symbol is the discrete measure μ_H = Σ_γ δ_γ/(1/4+γ²) on ℝ, pulled to 𝕋^∞ by t ↦ (p^{−it})_p. This is singular, so the bounded-symbol theory (Hilberdink Thm 2.1, Nikolski–Pushnitski) does not apply directly.
  - Since G_N is the natural truncation m, n ≤ N, Nikolski–Pushnitski's warning applies: no Szegő-type spectral law for G_N should be expected from that theory.
- **Four matrices of the same shape (computed here).** Each is D^{±1}·T·D^{±1} with T multiplicative Toeplitz.

  | Matrix | Kernel K(m/n) | Scaling | Positivity |
  |---|---|---|---|
  | Smith's (gcd(m,n)) | (pq)^{−1/2}, m/n = p/q in lowest terms (since gcd(m,n) = √(mn/(pq))) | D·T·D | unconditional |
  | Brownian min(m, n) | min(r, 1/r)^{1/2} = e^{−\|log r\|/2} | D·T·D | unconditional |
  | G_N | K_H | D·T·D | holds for all N exactly under RH |
  | Nyman–Beurling Gram matrix (Q3) | r^{−1/2}A(r) | D^{−1}·T·D^{−1} | unconditional |

  Lindqvist–Seip's M_s is T itself with K(p/q) = (pq)^{−s}, and S_s = D^{2s}M_sD^{2s}. Only for G_N is positivity itself the arithmetic content.
- **Pivots in the classical models (computed here from the factorisations above).**
  - Smith: gcd(i,j) = Σ_{d|i, d|j} φ(d), so (gcd) = EΦEᵀ with E_{id} = [d | i] unit lower triangular and Φ = diag(φ(1), …, φ(N)). By uniqueness of LDLᵀ, the Cholesky (Gram–Schmidt) pivots of Smith's matrix are d_k = φ(k). They satisfy d_k ≥ d_1 = 1 trivially, and e_1 is a shortest vector of the integral lattice (minimum 1).
  - min: min(i,j) = Σ_k [k ≤ i][k ≤ j] gives unit pivots. The lattice is ℤ^N, with minimum 1 attained by e_1 and also by e_k − e_{k−1}.

  So "d_k ≥ d_1" and "e_1 is shortest" are trivial in the two classical relatives. For G_N they are, per the repository, equivalent to RH.
- **Analogy with Lindqvist–Seip.** For 1/2 < s ≤ 1 their dilation system is not a Riesz sequence and λ_min → 0, with no rate given. G_N's orbit is likewise not Riesz, but the repository gives a rate (√log N/N ≪ λ_min ≪ log N/N). Note the different normalisations: λ_min of the D-scaled G_N against λ_min of the unscaled M_s.

### Gaps
- Hilberdink's 2006, 2009 and 2016 papers were not read beyond titles and the chapter's summaries. The 2006 paper's exact determinant theorem is unverified.
- No Hilberdink coauthor named "Toyokazu" was found in the arXiv listing; the brief's attribution could not be matched.
- Bondarenko–Seip's resonance-method papers ("GCD sums and complete sets of square-free numbers"; "Note on the resonance method") were not read this session. Their known setting, GCD forms and extreme values of ζ, uses no zeros, but this was not checked from the sources.
- Hong–Loewy's smallest-eigenvalue bound for power GCD matrices is known only from a search snippet — [Glasgow Math. J. PDF link](https://cambridge.org/core/services/aop-cambridge-core/content/view/B7AB74F7F4AF5752F69C9918114448E0/S0017089504001995a.pdf/asymptotic_behavior_of_eigenvalues_of_greatest_common_divisor_matrices.pdf).

## Q2. Weil and Li criteria as Gram matrices, the kernel Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)), and explicit numerical studies of such matrices

### Takeaway
I found no paper that forms the matrix (Σ_ρ m^ρ n^{1−ρ}/(ρ(1−ρ)))_{m,n≤N}, or Weil's form on the span of the integer step functions 1_{(0,n]}, or tabulates its eigenvalues, determinants or pivots.

The closest source is Burnol's semi-expository "The explicit formula in simple terms" (1998), which has every ingredient except the matrix:
- the evaluation Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π;
- the remark that RH ⟺ Σ_ρ 1/|ρ|² = 2 + γ − log 4π;
- Weil's formula for step functions, ĝ(s) = (X^s − 1)/s;
- Weil's positivity lemma;
- a reading of Weil positivity as the covariance of a stationary "arithmetic stochastic process".

Other matrix reformulations of RH concern different families: Matiyasevich's Toeplitz/Hankel matrices of Taylor coefficients, Pólya-frequency Toeplitz minors, and Li's coefficients.

### Cited Findings
- **Burnol, "The explicit formula in simple terms"**, arXiv:math/9810169 (1998, revised Nov. 1998) — [full text](https://arxiv.org/abs/math/9810169).
  - **The constant.** "another explicit evaluation, this time for an absolutely convergent sum: Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log(4π)". It follows from the functional equation and the Hadamard product.
  - **"A little joke reformulation of the Riemann Hypothesis. Lemma:** The Riemann Hypothesis holds if and only if Σ_ρ 1/|ρ|² = 2 + γ − log(4π)."
    - Proof: ½(1/|ρ|² + 1/|1−ρ|²) = Re(1/(ρ(1−ρ))) + ½(1−2Re ρ)²/(|ρ|²|1−ρ|²).
  - **Step functions.** "Weil proved his formula for a large class of g's, including in particular the step-function for which ĝ(s) = (X^s − 1)/s". Applying it recovers von Mangoldt's formula "if one uses Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log(4π)".
  - **Weil's positivity lemma.** RH ⟺ Σ_ρ ĝ(ρ)·conj(ĝ(1−ρ̄)) ≥ 0 for all smooth compactly supported g on (0,∞); the conjugation bar is lost in my extraction.
    - Burnol proves it directly: Mellin transforms of C_c^∞ functions interpolate arbitrary values at finitely many points.
    - Given an off-line zero, he builds g_N with Σ_ρ ĝ_N(ρ)ĝ_N(1−ρ) = −2 + O(1/4^N).
  - **"Weil's positivity criterion and stochastic processes".**
    - With C(g) = Σ_ρ ĝ(ρ − ½), the criterion is C(g ∗ g^c) ≥ 0, where g^c(u) = g(1/u).
    - "One obvious way … to obtain this positivity is to imagine that we have a probability measure µ on the (tempered) distributions Ω on (0,∞) … invariant under multiplicative translations, and the identity ∫_Ω X_F(d)X_G(d) dµ(d) = C(F ∗ G^c)".
    - "If such an 'arithmetic stochastic process' could be constructed, then the Riemann Hypothesis for all Dirichlet L-series would follow."
- **Morán Ledezma, "A probabilistic interpretation of Weil's explicit sums and arithmetic spectral measures"** — [arXiv:2311.08519, abstract and grep of full text](https://arxiv.org/abs/2311.08519).
  - On the Bohr compactification of ℝ, "the Weil explicit sum can be expressed in terms of covariances and expected values attached to random variables". It is "a limit of spectral integrals attached to operators" on L² of that compactification.
  - The text revisits the "zero mean stochastic process … whose covariance" is C(f ∗ g*).
- **Matiyasevich, "Hidden Life of Riemann's Zeta Function"** — [arXiv:0707.1983, abstract and grep](https://arxiv.org/abs/0707.1983); [Part 2, arXiv:0709.0028, abstract](https://arxiv.org/abs/0709.0028); [project page](https://logic.pdmi.ras.ru/~yumat/personaljournal/zetahiddenlife/zetahiddenlife.php).
  - "The Riemann Hypothesis can be reformulated as statements about the eigenvalues of certain matrices whose entries are defined in terms of the Taylor coefficients of the zeta function. These eigenvalues exhibit interesting visual patterns allowing one to state a number of conjectures."
  - Part 1 uses Toeplitz matrices, including a "determinant representation" in §1.6. Part 2 uses Hankel matrices obtained by rearranging columns. These are additive Toeplitz/Hankel matrices in Taylor coefficients, not a(m/n).
- **Pólya-frequency (total positivity) reformulations.** Two unrefereed 2026 preprints by Michalowski:
  - For the coefficients (a_k) of the normalised ξ-function, "The Riemann Hypothesis is equivalent to (a_k) being a Polya frequency sequence of infinite order, and hence to nonnegativity" of all Toeplitz minors — [arXiv:2607.16795, abstract](https://arxiv.org/abs/2607.16795).
  - The de Bruijn–Newman kernel Φ(|u|) is certified not to be PF₅ — [arXiv:2602.20313, abstract](https://arxiv.org/abs/2602.20313).
- **A withdrawn lead.** A web search returned two Zenodo records, "Operator-Theoretic and Computational Realizations of the Riemann Hypothesis", described in the search summary as an RH-equivalent "Gram matrix" of Weil's form built from pole, archimedean and prime terms — [record 21143338](https://zenodo.org/records/21143338). Both records (21143338, 21144644) return HTTP 410 (Gone) through the Zenodo API as of 2026-11-13. Their content, including the test functions used, could not be checked.
- **Covered by the earlier notes and not repeated.** Li and Bombieri–Lagarias; Yoshida's Hermitian forms; Connes–Consani's finite sections of the Weil form on windows (smallest eigenvalue 2.389 × 10⁻⁴⁸ at λ² = 11); Zhu 2026; Suzuki 2026. The earlier notes also derived, without finding a source, that under RH the Toeplitz matrices (λ_{j−k+1} − 2λ_{j−k} + λ_{j−k−1}) of second differences of Li coefficients are positive semidefinite — [earlier notes, Q2–Q3](../Sampling%20Dirichlet%20polynomials%20at%20zeta%20zeros/gram_and_nyman_beurling.md).
- **Under RH, linear statistics of zeros** converge to a Gaussian field with H^{1/2} covariance — [Bourgade–Kuan, arXiv:1203.5328, abstract](https://arxiv.org/abs/1203.5328). This is a fluctuation result, not a positivity criterion.

### Inferences
- **G_N is Weil's form on integer step functions (computed here).** For f_x = Σ_{n≤N} x_n 1_{(0,n]}, the Mellin transform ∫_0^∞ f(u)u^{s−1}du is F(s) = Σ x_n n^s/s (Re s > 0). Then

  Σ_ρ F(ρ)F(1−ρ) = Σ_{m,n} x_m x_n Σ_ρ m^ρ n^{1−ρ}/(ρ(1−ρ)) = xᵀG_N x,

  which equals Σ_ρ |F(ρ)|² under RH.
  - So G_N is the Gram matrix of Weil's functional on the span of 1_{(0,n]}, n ≤ N, up to the pole terms, which diverge for 1_{(0,n]} at s = 0.
  - The compactly supported variant 1_{[1,n]} = 1_{(0,n]} − 1_{(0,1)}, with Burnol's ĝ(s) = (n^s − 1)/s, corresponds to the coefficient vector e_n − e_1. So on the hyperplane Σ x_n = 0, f_x is supported in [1, N], the pole term ĝ(0) = Σ x_n log n is finite, and Weil's formula in Burnol's step-function form applies directly (computed here).
- **The (1,1) entry is RH-sensitive on its own.** (G_N)_{11} = K_H(1) = Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π unconditionally. By Burnol's lemma, the identity "‖w_1‖² = Σ_ρ |ρ|^{−2}" holds iff RH. That makes d_1 = K_H(1) a natural RH-calibrated benchmark for the repository's pivot criterion.
- **Flat model = Mellin–Plancherel = Brownian covariance (computed here).** Replacing Σ_ρ by (1/2π)∫ dt on Re s = 1/2 gives (1/2π)∫ |F(½+it)|² dt = ‖f_x‖²_{L²(0,∞)} = Σ x_m x_n min(m, n), since (1/2π)∫(m/n)^{it}(¼+t²)^{−1}dt = e^{−|log(m/n)|/2}.
  - In Burnol's picture, G_N would be the covariance matrix of X_n = d(1_{(0,n]}) for his hypothetical stationary "arithmetic process".
  - The flat model is the case where that process is Brownian motion.
  - No source states this step-function or Brownian specialisation.
- **Positive-definiteness on ℝ versus on log ℕ (computed here).**
  - RH ⟺ u ↦ K_H(e^u) is positive definite on ℝ.
    - (⇒) Under RH, K_H(e^u) = Σ_γ e^{iγu}/(¼+γ²) (Bochner).
    - (⇐) A positive-definite function is bounded, while an off-line zero ρ₀ gives the Laplace transform ∫_0^∞ K_H(e^u)e^{−zu}du a pole at z = ρ₀ − ½ with Re z > 0.
  - The repository's equivalence "G_N ⪰ 0 for all N ⟺ RH" is the stronger statement that positivity on the discrete set {log n}, i.e. integer step functions, suffices.
  - The nearest structural analogue in the literature is Báez-Duarte's strengthening of Nyman–Beurling, in which integer dilations suffice — [as recorded in the earlier notes](https://arxiv.org/abs/math/0202141). That is an approximation criterion, not a positivity one.

### Gaps
- Weil's 1952 paper and Bombieri's "Remarks on Weil's quadratic functional … I" (Rend. Lincei 2000) were not read. Either might contain a step-function special case, though none was quoted by Burnol, Connes–Consani or Suzuki.
- No matrix of this kernel was found in the work of Galway, Balazard, Báez-Duarte or Lagarias. The search was by abstract (arXiv API) and general web search, not full text.
- The withdrawn Zenodo preprints could not be assessed.
- de Branges's positivity conditions, reported to fail by Conrey–Li (2000), are a relevant cautionary example of a kernel-positivity route to RH. They were not located or checked this session.

## Q3. Vasyunin-type Nyman–Beurling Gram matrices: do they share the √(mn)·K(m/n) structure, and are there Cholesky or LDLᵀ studies?

### Takeaway
Yes, structurally, though with the inverse diagonal scaling. Its entries are given by the multiplicative autocorrelation A(λ) = ∫_0^∞{t}{λt}dt/t² introduced by BBLS. A short substitution (computed here) makes the Nyman–Beurling Gram matrix D^{−1}·(r^{−1/2}A(r))_{r=m/n}·D^{−1}, whose symbol is |ζ(½+it)|²/(¼+t²).

It is positive definite unconditionally; RH there is a distance statement, not a positivity statement. I found no Cholesky, LDLᵀ or Gram–Schmidt-pivot study of these matrices.

### Cited Findings
- **The multiplicative autocorrelation.** A(λ) = ∫_0^∞ {t}{λt} dt/t² is "la fonction d'autocorrélation multiplicative de la fonction « partie fractionnaire », introduite par Báez-Duarte et al. … dans le contexte de l'étude du critère de Nyman" — [Balazard–Martin, arXiv:1305.4395, full text grep](https://arxiv.org/abs/1305.4395).
  - A(λ) = λA(1/λ), and A(λ) ∼ ½λ log(1/λ) as λ → 0.
  - The paper describes A's points of differentiability via Wilton's function.
  - Original: Báez-Duarte, Balazard, Landreau, Saias, "Étude de l'autocorrélation multiplicative de la fonction 'partie fractionnaire'", *Ramanujan J.* 9 (2005) 215–240 — [DOI](https://doi.org/10.1007/s11139-005-0834-4) (title only).
  - Related: Balazard, "Sur les dilatations entières de la fonction partie fractionnaire", *Funct. Approx.* 35 (2006) 37–49 — [DOI](https://doi.org/10.7169/facm/1229442615) (title only).
- **Gram-determinant formula.** The NB distance is a ratio of Gram determinants, d_n² = det G(ρ_1,…,ρ_n,χ)/det G(ρ_1,…,ρ_n) — [Dimitrov–Oliveira, arXiv:1608.07887, via earlier notes](https://arxiv.org/abs/1608.07887).
- **Other Gram-matrix work.** Ehm 2024 gives Gram-matrix formulae, and Alouges–Darses–Hillion use block-Hankel Gram forms — [earlier notes, Q3](../Sampling%20Dirichlet%20polynomials%20at%20zeta%20zeros/gram_and_nyman_beurling.md). No eigenvalue or pivot bounds were found there.
- **Hardy-space variant.** A Hardy-space version of the Nyman–Beurling–Báez-Duarte criterion "states that the RH holds if and only if a particular sequence of functions (h_k)_{k≥2}" … (the abstract was cut off at this point in my retrieval). The paper studies orthogonality questions tied to ζ-zeros — [Calderaro–Manzur–Noor–Santos, arXiv:2203.05030, abstract](https://arxiv.org/abs/2203.05030).
- **Negative searches.** arXiv abstract searches for "Riemann hypothesis" with "Gram-Schmidt", "Cholesky", or "Schur complement" + zeta returned nothing relevant — [arXiv API query used](https://export.arxiv.org/api/query?search_query=abs:%22Gram-Schmidt%22+AND+abs:%22Riemann+hypothesis%22).

### Inferences
- **Structure (computed here).**
  - With ρ_a(x) = {1/(ax)} on (0,∞), substituting t = 1/(ax) gives ⟨ρ_a, ρ_b⟩ = A(a/b)/a = Ã(a/b)/√(ab), where Ã(r) = r^{−1/2}A(r) is even in log r (by A(λ) = λA(1/λ)).
  - Since the Mellin transform of {1/x} is −ζ(s)/s on 0 < Re s < 1, Plancherel gives Ã(r) = (1/2π)∫ r^{−it}|ζ(½+it)|²/(¼+t²) dt.
  - So the NB Gram matrix is D^{−1}·T(|ζ(½+it)|² dt/2π(¼+t²))·D^{−1}, the flat model is D·T(dt/2π(¼+t²))·D, and G_N is D·T(Σ_γ δ_γ/(¼+γ²))·D.
  - The NB symbol vanishes exactly at the zeros, while G_N's symbol is supported on them.
- **Pivots differ in meaning.** Gram–Schmidt pivots of the NB system are squared distances of ρ_k from span{ρ_j : j < k}. They are positive unconditionally and are not RH-sensitive by themselves. RH is the decay of the distance of the separate vector χ. The repository's pivot criterion compares pivots of a form whose positivity is RH. No source found treats either kind of pivot sequence.

### Gaps
- Vasyunin's paper with the explicit cotangent-sum Gram formula (St. Petersburg Math. J. 7 (1996)) and Landreau–Richard's numerics (Exp. Math. 11 (2002)) were not read, here or in the earlier notes. Landreau–Richard may contain conditioning data for the NB Gram matrix.
- BBLS 2005 itself was not read; the link between A and the Gram entries is my substitution above.

## Q4. Smallest eigenvalues, determinants and pivots of zeta-built matrices, and sampling of Dirichlet polynomials at zeros in matrix form

### Takeaway
The only sharp smallest-eigenvalue theorem for a matrix of the form (K(m/n)) is Lindqvist–Seip's: λ_min → ζ(2s)/ζ(s)² for s > 1 and → 0 for 1/2 < s ≤ 1, with no rate.

Other results found:
- largest-eigenvalue asymptotics (Hilberdink; Aistleitner–Berkes–Seip; Bondarenko–Hilberdink–Seip);
- eigenvalue-counting asymptotics for LCM matrices (Hilberdink–Pushnitski);
- Smith's determinant;
- Redheffer's matrix, the one classical matrix family with det R_n = M(n) and RH ⟺ det R_n = O(n^{1/2+ε});
- super-exponentially small eigenvalues for Weil windows (earlier notes).

Nothing comparable to √(log N)/N ≪ λ_min(G_N) ≪ log N/N or to the constant 0.0429 was found. Nor was any pivot theorem tied to RH.

"Sampling at zeros in matrix form" appears in the literature only on the interpolation side: Matiyasevich's finite Dirichlet series vanishing at the first zeros, and the NB interpolation bounds from the earlier notes.

### Cited Findings
- **Lindqvist–Seip theorem**, stated verbatim in Q1 — [full text](http://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8425.pdf). The sharp bounds are lim inf/lim sup statements, "not attained for any finite N", and the authors doubt an "arithmetic proof".
- **Smith's matrix.** det(gcd(m,n))_{N×N} = Π_{k≤N} φ(k), with an explicit triangular factorisation (Smith 1876; Bourque–Ligh 1992), as recorded by [Lindqvist–Seip](http://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8425.pdf).
- **Largest eigenvalues.**
  - Hilberdink's Cor. 4.1–4.2 and Thm 3.1, quoted in Q1 — [chapter](https://centaur.reading.ac.uk/50981/).
  - Largest eigenvalues of GCD matrices as a byproduct of the Poisson-integral method — [Aistleitner–Berkes–Seip](https://arxiv.org/abs/1210.0741).
- **Eigenvalue asymptotics.** λ_n(E(σ,τ)) = κn^{−ρ} + o(n^{−ρ}) for LCM matrices, applied to singular values of truncated multiplicative Toeplitz matrices with symbol ζ(σ+it), σ < 1/2 — [Hilberdink–Pushnitski](https://arxiv.org/abs/2110.14323).
- **Redheffer's matrix.**
  - R_n = A_n(1) + E_n, with A_n(f)A_n(g) = A_n(f∗g) (Dirichlet convolution). Hence det R_n = M(n), and "RH holds if and only if det R_n = O(n^{1/2+ε})" — [Hilberdink chapter, full text](https://centaur.reading.ac.uk/50981/).
  - Original: Redheffer, "Eine explizit lösbare Optimierungsaufgabe" (1977) — [DOI](https://doi.org/10.1007/978-3-0348-5936-3_13) (title only).
  - Spectral studies, titles only: Barrett–Forcade–Pollington, *Linear Algebra Appl.* 107 (1988) 151–159 — [DOI](https://doi.org/10.1016/0024-3795(88)90241-8); Vaughan, "On the eigenvalues of Redheffer's matrix, I" — [DOI](https://doi.org/10.1201/9780203747018-25).
  - A secondary summary attributes to Vaughan the bounds O((log n)^{2/5}) unconditionally and O(log log n) on RH for the non-trivial eigenvalues — [snippet via AIM/Wikipedia](https://en.wikipedia.org/wiki/Redheffer_matrix). Unverified.
- **Szegő-type theory.** It fails for natural truncations — [Nikolski–Pushnitski](https://arxiv.org/abs/2001.01474).
- **Finite Dirichlet series vanishing at initial zeros.** Beliakov–Matiyasevich, *Exp. Math.* 24(2) (2015) 150–161 — [arXiv:1402.5295, abstract](https://arxiv.org/abs/1402.5295) ([DOI](https://doi.org/10.1080/10586458.2014.976801)).
  - "The finite Dirichlet series from the title are defined by the condition that they vanish at as many initial zeroes of the zeta function as possible. It turned out that such series can produce extremely good approximations to the values of Riemann's zeta function inside the critical strip."
  - "the coefficients of these series have remarkable number-theoretical properties discovered in large scale high accuracy numerical experiments. So far no theoretical explanation to the observed phenomena was found."
  - Companion paper: Matiyasevich, "Riemann's zeta function and finite Dirichlet series", *St. Petersburg Math. J.* 27(6) (2016) 985–1002 — [DOI](https://doi.org/10.1090/spmj/1431) (title only).
- **Weil-window eigenvalues and NB interpolation.** These are in the earlier notes: [Connes–Consani](https://arxiv.org/abs/2106.01715), [Zhu (preprint)](https://arxiv.org/abs/2608.24827), [Burnol 2002](https://arxiv.org/abs/math/0103058), [Dimitrov–Oliveira](https://arxiv.org/abs/1608.07887).

### Inferences
- **Sizes relative to the literature.** The repository's λ_min(G_N) ≍ log N/N (up to √log N) sits between Lindqvist–Seip's bounded-below regime (s > 1) and the Weil-window regime (exp(−cN)-type).
  - The closest analogue in kind is Lindqvist–Seip's 1/2 < s ≤ 1 case: a dilation system that is not a Riesz sequence, with λ_min → 0 and no rate.
  - No source gives a rate of decay for λ_min of any multiplicative Toeplitz-type matrix built from ζ or its zeros.
- **Pivot growth.**
  - Smith's matrix has pivots φ(k) (computed here, Q1), so pivots growing with k are classical there.
  - G_N's pivots grow like log k under RH, with upper bound log(k/2π) + 1 − γ + o(1) per the repository.
  - No source treats pivots of a zero-built Gram matrix, or the inequality d_k ≥ d_1.
- **Consistency with Matiyasevich.** His length-N series vanishing at the first N−1 zeros does not conflict with the repository's corollary that, under RH, no nonzero length-N Dirichlet polynomial vanishes at all zeros up to height 2000N. The latter set has ≍ N log N zeros, far more than N − 1, by the Riemann–von Mangoldt count. The two sit on opposite sides of the sampling/interpolation divide described in the earlier report.

### Gaps
- Not read: Hong–Loewy (2004) and the Redheffer spectral papers (Barrett–Forcade–Pollington; Barrett–Jarvis; Vaughan I/II).
- Hilberdink 2006's determinant results are known only from the chapter's mention of the Euler-product factorisation.
- No study was found of det G_N, of log det asymptotics, or of λ_min for any explicit-formula Gram matrix indexed by integers.

## Q5. Lattices from number theory linked to RH (Weng, Ki, Suzuki, Bost) and statements that a specific vector is shortest

### Takeaway
The RH-and-lattices literature is about zeta functions of lattices.
- Weng's non-abelian zeta functions integrate (e^{h⁰(Λ)} − 1)e^{−s·deg Λ} over moduli of semistable lattices.
- Their RH has been proved in low rank and for some group versions: Lagarias–Suzuki (rank 2), Suzuki (rank 3; Sp(4)), Ki–Komori–Suzuki (Chevalley groups), and Weng–Zagier (elliptic curves over finite fields).
- Their zeros are not those of ζ.

Bost's theta invariants and slopes give the Arakelov language for Euclidean lattices; no RH equivalence was found there.

Lattice reduction has been applied to the zeros (Best–Trudgian; Odlyzko–te Riele) to bound linear relations, not to characterise RH.

I found no statement, conjectured or proved, that RH is equivalent to a specific vector being shortest in a lattice built from the zeros or the primes.

### Cited Findings
- **Weng's rank-n zeta function.**
  - Definition: ζ̂_{ℚ,n}(s) = ∫_{M_{ℚ,n}} (e^{h⁰(ℚ,Λ)} − 1)(e^{−s})^{deg(Λ)} dµ(Λ), over "the moduli space of semi-stable lattices Λ of rank n".
  - Properties: functional equation s ↔ 1 − s, and simple poles at 0 and 1.
  - Weng's page says "a weak version" of the rank-n RH is Thm 15.4 of his book.
  - Sources: [Weng, project page](https://www3.math.kyushu-u.ac.jp/~weng/Zetas2.html); *Zeta Functions of Reductive Groups and Their Zeros*, World Scientific — [DOI](https://doi.org/10.1142/10723) (title only).
- **Lagarias–Suzuki.** Integrating the non-holomorphic Eisenstein series E(z,s) "with respect to certain non-negative measures gives meromorphic functions of s that have all their zeros on the critical line" — [arXiv:math/0412039, abstract](https://arxiv.org/abs/math/0412039). That this covers Weng's rank-2 zeta is stated in the repository's [ball-conjecture.md](../../docs/ball-conjecture.md) (J. Number Theory 118 (2006)) and in a snippet of Weng's notes.
- **Suzuki.**
  - "A Proof of the Riemann Hypothesis for the Weng Zeta Function of Rank 3 for the Rationals", *The Conference on L-Functions* (World Scientific, 2007), 175–199 — [DOI](https://doi.org/10.1142/9789812772398_0010) (title only).
  - "The Riemann hypothesis for Weng's zeta function of Sp(4) over ℚ" — [arXiv:0802.0102, abstract](https://arxiv.org/abs/0802.0102).
- **Ki–Komori–Suzuki**, "On the zeros of Weng zeta functions for Chevalley groups", *Manuscripta Math.* 148 (2015) 119–176 — [DOI](https://doi.org/10.1007/s00229-015-0736-8) (title only; scope of the theorem not verified).
- **Weng–Zagier.**
  - "Higher-rank zeta functions for elliptic curves", *PNAS* 117(9) (2020) 4546–4558 — [DOI](https://doi.org/10.1073/pnas.1912023117).
  - "Higher-rank zeta functions and SL_n-zeta functions for curves", *PNAS* 117(12) (2020) 6398–6408 — [DOI](https://doi.org/10.1073/pnas.1912501117).
  - Titles only. Weng's notes, per a search snippet, state that the rank-n zeta of an elliptic curve over 𝔽_q satisfies RH.
  - Genus-2 curves: RH holds as the rank n → ∞ — [Shi Zhan, arXiv:2511.06729, abstract](https://arxiv.org/abs/2511.06729).
- **Rank-one background.** h⁰ of Arakelov divisors via theta series is the basis of these constructions — [van der Geer–Schoof, *Selecta Math.* 6 (2000) 377–398, DOI](https://doi.org/10.1007/pl00001393) (title only).
- **Bost**, *Theta Invariants of Euclidean Lattices and Infinite-Dimensional Hermitian Vector Bundles over Arithmetic Curves*, Progress in Mathematics, Birkhäuser 2020 — [DOI](https://doi.org/10.1007/978-3-030-44329-0) (title only).
- **Lattices and the zeros.** Best–Trudgian, "Linear relations of zeroes of the zeta-function", *Math. Comp.* 84 (2015) 2047–2058 — [arXiv:1209.3843, abstract](https://arxiv.org/abs/1209.3843) ([DOI](https://doi.org/10.1090/s0025-5718-2014-02916-5)).
  - "This article considers linear relations between the non-trivial zeroes of the Riemann zeta-function. The main application is an alternative disproof to Mertens' conjecture."
  - They show lim sup M(x)x^{−1/2} ≥ 1.6383 and a matching lim inf bound.
- **Negative searches.**
  - arXiv abstract searches for "Riemann hypothesis" with "shortest vector" returned only an ERH-conditional algorithmic paper — [Wesolowski, arXiv:1807.01561, abstract](https://arxiv.org/abs/1807.01561).
  - "Riemann hypothesis" with lattice + "equivalent", Gram, or Hodge index returned nothing relevant.
  - A general web search found "no known lattice criterion equivalent to the Riemann hypothesis" — [search results incl. Fukshansky's notes](https://www1.cmc.edu/pages/faculty/lenny/classes/spring_2019/m195/GNT_lecture-notes.pdf).

### Inferences
- **Different kinds of statement.** Weng-type results give RH for new zeta functions defined by averaging over lattices. The repository's lattice statement concerns one explicit lattice for ζ itself: ℤ^N with the form G_N, computed from the primes, with ±e_1 its only shortest vectors under RH. I found nothing of the second kind.
- **The slope reading has no RH-equivalent counterpart.** In the Stuhler–Grayson–Bost formalism (as used in the repository's docs), the reading of d_k ≥ d_1 as "no quotient of the flag ℤw_1 ⊂ ℤw_1 + ℤw_2 ⊂ ⋯ has larger slope than F_1" has no RH-equivalent counterpart in the sources found. This rests on titles and abstracts only; Bost's book was not read.

### Gaps
- Not read: Bost's book, van der Geer–Schoof, and Grayson's 1984 reduction-theory paper.
- Odlyzko–te Riele's use of LLL on the zeros (J. reine angew. Math. 357 (1985)) was not verified this session. Best–Trudgian's method (lattice reduction or otherwise) is not stated in the abstract I read.
- Ki's paper on Weng zeta functions (believed IMRN 2010) was not found via Crossref.
- The claim "Ki, Lagarias, Suzuki prove RH for ranks 2–5 over ℚ" is from a truncated snippet of Weng's notes and is unverified.

## Verdict: does G_N, its pivot equivalence, or its lattice equivalence, or a close variant, appear in the literature?

### Takeaway
**No, as far as these searches reach.** None of the following was found in any source:
- the matrix G_N = (√(mn)·K_H(m/n)), i.e. (Σ_ρ m^ρ n^{1−ρ}/(ρ(1−ρ)))_{m,n≤N};
- the equivalence RH ⟺ G_N ⪰ 0 for all N, i.e. Weil positivity restricted to integer step functions;
- any bound or asymptotic for λ_min(G_N);
- any statement about its Cholesky pivots, including RH ⟺ d_k ≥ d_1;
- RH ⟺ e_1 is a shortest vector.

Each ingredient is classical and should be cited. In rough order of closeness, the nearest results are:
1. Weil's positivity criterion, and Weil's explicit formula for step functions ĝ(s) = (X^s − 1)/s, both as presented by Burnol (1998).
2. Burnol's lemma RH ⟺ Σ_ρ |ρ|^{−2} = 2 + γ − log 4π, which is exactly the statement that (G_N)_{11} = K_H(1) equals ‖w_1‖² computed over the zeros.
3. Burnol's reading of Weil positivity as the covariance of a multiplicatively stationary process, the conceptual parent of the Brownian (min(m, n)) flat model.
4. Lindqvist–Seip's GCD matrices, the same D·T·D structure (Smith's matrix is √(mn)·(pq)^{−1/2}), with the only sharp λ_min theorem. Pivots there are φ(k), and "e_1 shortest" is trivial.
5. Multiplicative Toeplitz theory (Hilberdink; Nikolski–Pushnitski; Hilberdink–Pushnitski; Aistleitner–Berkes–Seip; Brevig et al.), which uses ζ-symbols, never zero symbols, and has unconditional positivity.
6. Nyman–Beurling Gram matrices, the same structure with D^{−1} scaling and symbol |ζ(½+it)|²/(¼+t²), where RH is a distance statement.
7. Matrix reformulations of RH of other kinds: Redheffer (det = M(n)), Matiyasevich (eigenvalues of Taylor-coefficient Toeplitz/Hankel matrices), Pólya-frequency Toeplitz minors, and Li coefficients.
8. Weng zeta functions of semistable lattices with proved RH, and Bost's slopes, which give lattices and RH but no equivalence for ζ.

### Cited Findings
- Weil positivity lemma; step-function explicit formula; Σ1/(ρ(1−ρ)) = 2 + γ − log 4π; "joke" RH ⟺ Σ1/|ρ|² = 2 + γ − log 4π; stochastic-process reading — [Burnol, arXiv:math/9810169](https://arxiv.org/abs/math/9810169).
- GCD matrices: structure, Smith's determinant, sharp λ_min/Λ_max theorem — [Lindqvist–Seip 1998](http://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8425.pdf).
- Multiplicative Toeplitz matrices with ζ-symbols, and Redheffer — [Hilberdink 2015](https://centaur.reading.ac.uk/50981/); [Nikolski–Pushnitski](https://arxiv.org/abs/2001.01474); [Hilberdink–Pushnitski](https://arxiv.org/abs/2110.14323); [Aistleitner–Berkes–Seip](https://arxiv.org/abs/1210.0741); [Brevig et al.](https://arxiv.org/abs/1411.7294).
- NB multiplicative autocorrelation — [Balazard–Martin](https://arxiv.org/abs/1305.4395); [BBLS 2005](https://doi.org/10.1007/s11139-005-0834-4).
- Other matrix reformulations — [Matiyasevich](https://arxiv.org/abs/0707.1983); [Michalowski (preprint)](https://arxiv.org/abs/2607.16795).
- Sampling at zeros as interpolation — [Beliakov–Matiyasevich](https://arxiv.org/abs/1402.5295).
- Weng-type lattice zeta functions — [Weng](https://www3.math.kyushu-u.ac.jp/~weng/Zetas2.html); [Lagarias–Suzuki](https://arxiv.org/abs/math/0412039); [Suzuki rank 3](https://doi.org/10.1142/9789812772398_0010); [Ki–Komori–Suzuki](https://doi.org/10.1007/s00229-015-0736-8); [Weng–Zagier](https://doi.org/10.1073/pnas.1912023117).

### Inferences
- **Novel as far as found.** Each of the following appears to be new:
  - G_N as a matrix family;
  - the step-function restriction of Weil's criterion being sufficient for RH (G_N ⪰ 0 ∀N ⟺ RH);
  - the λ_min window √(log N)/N ≪ λ_min ≪ log N/N and the conjectured constant 0.0429;
  - the pivot bounds (d_k ≥ 0.0577 for k ≥ 2, d_k ≫ log k, d_k ≤ log(k/2π) + 1 − γ + o(1));
  - the pivot equivalence RH ⟺ d_k ≥ d_1;
  - the lattice equivalence RH ⟺ e_1 shortest, with ±e_1 unique under RH.
- **Suggested framing for the repository note.**
  - G_N is "Weil's quadratic functional on the integer step functions 1_{(0,n]}", or equivalently "the √(mn)-scaled multiplicative Toeplitz matrix with symbol the zero measure Σδ_γ/|ρ|²".
  - Cite Weil (1952) via Burnol for the step-function explicit formula and Burnol for the diagonal constant and the RH-sensitivity of Σ1/|ρ|².
  - Cite Lindqvist–Seip and Smith for the structural relatives, where pivots (φ(k)) and shortest vectors are trivial.
  - Cite Nikolski–Pushnitski for why natural truncations escape Szegő theory.
- **Where duplication could hide.** The most likely places are Bombieri's 2000 Lincei paper, Yoshida 1992, Weil 1952, BBLS 2005, Vasyunin 1996, Landreau–Richard 2002, and the withdrawn Zenodo preprints. None was readable this session. None is quoted by the papers read as containing a step-function Gram matrix or a lattice criterion.

### Gaps
- **Search coverage.** MathSciNet and zbMATH were not queried. arXiv searches were by title, abstract and author (API), not full text. General web search and Crossref were used for verification.
- **Title-only sources.** Several items are cited by title only, as marked above.
- **Withdrawn records.** The Zenodo records are withdrawn (HTTP 410), so their test functions cannot be compared with G_N.
- **Bottom line.** The absence of prior art is established only to this extent.
