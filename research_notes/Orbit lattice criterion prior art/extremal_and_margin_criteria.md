# Extremal problems for Dirichlet polynomials at the zeta zeros, orthogonal Dirichlet polynomials, and margin versions of RH criteria: prior art for the orbit-lattice (pivot) equivalence

**Scope.** The statement under test, as formalised in this repository:
- Let P(s) = Σ_{n≤k} x_n n^s, with real x_n and x_k = 1.
- Let d_k be the minimum of Σ_ρ |P(ρ)|²/|ρ|². Equivalently, d_k is the k-th Gram–Schmidt pivot of w_n = n^s for the measure μ_Z = Σ_ρ δ_ρ/|ρ|². Its Gram matrix is √(mn)·K_H(m/n), with K_H(r) = Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)), and it is defined unconditionally from the primes via ψ.
- **The equivalence:** RH ⟺ d_k ≥ d_1 for every k, where d_1 = K_H(1) = 2 + γ − log 4π ≈ 0.0462.
- Under RH, d_k ≥ 0.0577 for every k ≥ 2, and d_k ≍ log k.
- In the "flat model" (Lebesgue measure on the line with weight 1/(1/4+t²)), the Gram matrix is min(m,n) and every pivot equals d_1.
- Sources in the repo: [docs/ball-conjecture.md](../../docs/ball-conjecture.md), lines 18–25 and 401–530.

**Prior notes.** Earlier notes in `research_notes/Sampling Dirichlet polynomials at zeta zeros/` cover:
- Nyman–Beurling–Báez-Duarte (NB) basics: Burnol, BBLS and Bettin–Conrey–Farmer (BCF) lower bounds, and Dimitrov–Oliveira's Theorem 3;
- Gonek, Bui–Florea–Milinovich (BFM), Ng, Milinovich–Ng and Montgomery–Odlyzko/Conrey–Ghosh–Gonek (CGG) mean values at zeros;
- Weil positivity on windows (Yoshida, Connes–Consani, Suzuki 2026, Zhu 2026).

They are not repeated here, only referenced.

**Source tags.**
- "full text": I read the arXiv PDF this session.
- "abstract": only the abstract was read.
- "as restated by X": I rely on X's account.
- "search snippet": only a search-engine excerpt was seen.
- "computed here": my own computation or derivation. Those items appear only under Inferences.

## 1. Orthogonal Dirichlet polynomials, Christoffel functions and Szegő-type extremal problems for measures on (or built from) the zeros

### Takeaway
The flat model is already in the literature.
- **Lubinsky's formula.** Lubinsky's explicit orthogonal Dirichlet polynomials for the arctangent weight cover it with frequencies λ_n = √n.
- **Dimitrov–Oliveira's form.** They wrote out exactly this case, orthonormal ψ_n = n^{1/2−it} − (n−1)^{1/2−it} for dt/(2π(1/4+t²)), and used it for an NB-type extremal problem at zeta zeros.
- **Consequence.** The Gram matrix is min(m,n) and every monic pivot is constant.

For the discrete measure Σ_ρ δ_ρ w(ρ) carried by the zeros, nothing was found on orthogonal Dirichlet polynomials, Christoffel functions or Gram–Schmidt pivots.
- The only orthogonal-polynomial construction on a discrete measure at the zero ordinates found is Cardon–de Gaston. It uses ordinary polynomials in z and encodes "RH with simple zeros" through ratio asymptotics, not through norms.
- Szegő-type theory for Dirichlet series (Helson–Lowdenslager; Guo–Ni–Zhou's "Szegő problem in infinitely many variables") normalises the constant term and treats absolutely continuous weights on T^∞. It does not cover measures carried by the zeros, or the leading-coefficient normalisation used here.

### Cited Findings
- **Lubinsky, J. Approx. Theory 177 (2014) 43–56, "Orthogonal Dirichlet polynomials with arctangent density"** — [DOI](https://doi.org/10.1016/j.jat.2013.10.001); bibliographic data verified via the Crossref API.
  - **Setting:** frequencies 1 = λ_1 < λ_2 < … and the basis λ_k^{−it}.
  - **The polynomials** (as restated by Dimitrov–Oliveira §2.3, full text): φ_1 = 1 and φ_n(t) = (λ_n^{1−it} − λ_{n−1}^{1−it})/√(λ_n² − λ_{n−1}²) satisfy ∫ φ_n φ̄_m dt/(π(1+t²)) = δ_{nm}. Lubinsky also "described the asymptotic behaviour of the corresponding kernel polynomials" — [Dimitrov–Oliveira, arXiv:1608.07887](https://arxiv.org/abs/1608.07887).
  - **Abstract** (search snippet of a library catalogue record): Lubinsky "derives formulae for their Christoffel functions, and deduces their asymptotics, as well as universality limits, and spacing of zeros for their reproducing kernels", relates ordinary Dirichlet series to orthogonal expansions, and proves Markov–Bernstein inequalities — [catalogue record](https://vufind-test.katalog.k.utb.cz/SummonRecord/FETCH-LOGICAL-c340t-cb31e5c172d22d43d9d23cb9f07c807f47b6df000b9fe955ffbc839300fb25803).
- **Lubinsky's follow-ups.**
  - "Dirichlet orthogonal polynomials with Laguerre weight", J. Approx. Theory 194 (2015) 146–156 — [DOI](https://doi.org/10.1016/j.jat.2015.02.005).
  - Survey "Orthogonal Dirichlet Polynomials", in *Approximation and Computation in Science and Engineering*, Springer Optim. Appl. (2022) 573–587 — [DOI](https://doi.org/10.1007/978-3-030-84122-5_30).
  - The 2020 preprint of the survey covers the arctan density, rational weights, the exponential weight (linked to Müntz polynomials) and constant weight on [−T, T]. It treats the Christoffel function through its extremal property (search snippets) — [preprint PDF](https://lubinsky.math.gatech.edu/Research%20papers/DirichletOPSurveyApril2020.pdf); the server returned TLS/503 errors, so it was not read.
- **Dimitrov–Oliveira's specialisation (full text).**
  - "The choice λ_n = n^{1/p} and a simple change of variables shows that the Dirichlet polynomials ψ_1 = 1, ψ_n(t) = (n^{1/p−it} − (n−1)^{1/p−it})/√(n^{2/p} − (n−1)^{2/p}) satisfy (1/pπ)∫ ψ_n ψ̄_m dt/(1/p² + t²) = δ_{nm}."
  - The kernel K_n(u,v) = Σ_{k≤n} ψ_k(u)ψ̄_k(v) obeys, uniformly on compacts, K_n(u,u) = (p/2)|1/p + iu|² log n (1 + o(1)) (their (2.9), citing Lubinsky (1.19)–(1.20)) and |K_n(u,v)| ≤ p|1/p+iu||1/p−iv|/|u − v| + o(log n) (their (2.10)).
  - Lemma 3: for distinct t_1, …, t_m the matrix (K_n(t_i,t_j)) is nonsingular for n > n(m), with det H/(log n)^m = (p^m/2^m)∏|1/p+it_j|² + o(1).
  - — [arXiv:1608.07887](https://arxiv.org/abs/1608.07887).
- **Cardon–de Gaston, "An equivalence for the Riemann hypothesis in terms of orthogonal polynomials"** (manuscript dated 27 Aug 2004; full text) — [PDF](https://mathdept.byu.edu/cardon/papers/Orthogonal_RH.pdf).
  - **The measure.** Fix f analytic on x ≥ 0, |y| ≤ 1/2, real on the reals, with Re f > 0 and |f(x+iy)| < e^{−cx}. Then F(T) = Σ_{α_k<T, β_k=0} f(α_k) + Σ_{α_k<T, β_k>0} [f(α_k + iβ_k) + f(α_k − iβ_k)] is a step function on the zeros α_k + iβ_k of Ξ(z) = ξ(1/2+iz).
  - **The polynomials.** p_n are the orthogonal polynomials for ⟨p, q⟩ = ∫ p q dF.
  - **Theorem 1:** "The Riemann hypothesis with simple zeros is true if and only if lim_{n→∞} p_{2n}(z)/p_{2n}(0) = ξ(1/2+iz)/ξ(1/2) for every z ∈ ℂ."
- **Szegő's theorem for groups with ordered duals.**
  - "Theorem 3.6 (Szegö). Suppose G is a compact group with ordered dual, µ ≥ 0 a finite Borel measure on G, dµ = w dm_G + dµ_s. Then exp ∫_G log w dm_G = inf_{Q∈P_0} ∫_G |1 + Q|² dµ."
  - Sun–Zu–Lu cite Rudin, *Fourier Analysis on Groups*, Thms 8.3.2, 8.4.3 and 8.5.2, and Helson–Lowdenslager, "Prediction theory and Fourier series in several variables", Acta Math. 99 (1958) 165–202. They give "a new proof of the infinite-dimensional Szegö's theorem" — [Sun–Zu–Lu, arXiv:2502.17018 (2025), full text](https://arxiv.org/abs/2502.17018).
- **Szegő's problem for Dirichlet series** (Guo–Ni–Zhou, full text) — [arXiv:2201.01993](https://arxiv.org/abs/2201.01993).
  - **Setting.** The space is H^p(T^∞), which corresponds to Dirichlet series by the Bohr correspondence. P_0 is the set of polynomials q with q(0) = 0; these are Dirichlet polynomials with no constant term.
  - **The quantity.** For K ≥ 0 with log K ∈ L¹(T^∞) and ‖K‖_1 = 1, put S(K) = inf_{q∈P_0} ∫_{T^∞} |1 − q|^p K dm_∞. It lies in [exp ∫ log K dm_∞, 1].
  - **Theorem 3.1:** S(K) equals the lower bound "if and only if K = |h|^p for some cyclic vector h ∈ H^p(T^∞)".
  - **References.** They cite Bingham, "Szegö's theorem and its probabilistic descendants", Probab. Surv. 9 (2012) 287–324, for the prediction-theory side.
- **Hilbert space of Dirichlet series.** ℋ = {Σ a_n n^{−s} : Σ|a_n|² < ∞} is modelled as H² of the infinite polydisc (Hedenmalm–Lindqvist–Seip, Duke Math. J. 86 (1997)) — [arXiv:math/9512211](https://arxiv.org/abs/math/9512211), as in the earlier notes.
- **Searches with no hits.**
  - arXiv API, 13 Nov 2026: "Gram-Schmidt" + zeta + zeros, Christoffel + "Riemann zeta", "Riemann zeros" + "Jacobi matrix", "Riemann hypothesis" + "Brownian motion" + Gram, and "orthogonal Dirichlet polynomials" — all returned nothing — [arXiv API](https://export.arxiv.org/api/query?search_query=abs:%22orthogonal+Dirichlet+polynomials%22).
  - Crossref lists Lubinsky's papers and an unrelated Bostan–Chapoton paper on continued fractions and Dirichlet series (title only) — [Crossref](https://api.crossref.org/works?query.bibliographic=orthogonal+Dirichlet+polynomials).

### Inferences
- **The flat model is Lubinsky's formula at p = 2 (computed here).**
  - In L²(dt/(2π(1/4+t²))), put e_n(t) = n^{1/2−it}. Dimitrov–Oliveira's ψ_n telescope, so e_n = Σ_{j≤n} ψ_j with ψ orthonormal.
  - Hence ⟨e_m, e_n⟩ = min(m,n), and every Gram–Schmidt pivot equals ‖ψ_k‖² = 1.
  - Conjugating gives the user's w_n = n^s at s = 1/2+it.
  - For general frequencies the pivot with "x_k = 1" (coefficient λ_k on λ_k^{−it}) is λ_k² − λ_{k−1}². It is constant exactly when λ_k² is an arithmetic progression, which is the n^{1/2} case.
  - So "all minima equal in the flat model" is a known special case and should be credited to Lubinsky (2014), and to Dimitrov–Oliveira for the explicit p = 2 form.
- **A probabilistic reading of the flat model (computed here; classical Doob transform).**
  - ∫ e^{iγτ} dγ/(2π(1/4+γ²)) = e^{−|τ|/2}, the Ornstein–Uhlenbeck covariance. Sampling it at τ = log m − log n and multiplying by √(mn) gives min(m,n), the covariance of Brownian motion at integer times.
  - Under RH the true kernel is K(τ) = K_H(e^τ) = Σ_γ e^{iγτ}/(1/4+γ²), an almost-periodic positive-definite function with spectrum on the ordinates. d_k/k is then the one-step prediction error of the corresponding stationary process at time log k from times log 1, …, log(k−1).
  - This puts the problem inside Kolmogorov–Krein prediction theory (Bingham's survey), but no source treats this sampled problem.
- **Why Szegő/Helson theory does not transfer.**
  - On the circle, the monic and the constant-term normalisations give the same norm, because of the reversal Φ_n ↦ Φ_n^*.
  - For Dirichlet polynomials with integer frequencies there is no reversal, since n ↦ k/n is not integral. The user's normalisation x_k = 1 corresponds, after dividing by k^s, to the frequency set {k/n : n < k}. That is not the cone P_0 of Szegő/Guo–Ni–Zhou.
  - Every measure on the critical line, discrete or absolutely continuous, pushes forward to a measure on T^∞ that is singular with respect to Haar measure, so the exp ∫ log w theory gives no information. I found no theory of Christoffel functions for such measures.
- **Cardon–de Gaston versus the orbit.** Their construction is the closest "orthogonal polynomials for a discrete measure on the zeros" result, but it differs in three ways:
  - the basis is z^n (polynomials in the ordinate), not n^s;
  - the weight f is generic;
  - RH is encoded in ratio asymptotics of p_{2n}, not in a norm inequality.

### Gaps
- I did not read Lubinsky's papers directly: lubinsky.math.gatech.edu failed TLS verification through curl and returned 503 to WebFetch, and ScienceDirect returned 403. His formulas are taken from Dimitrov–Oliveira's restatement, and the Christoffel-function claims from abstract snippets.
- Cardon–de Gaston's publication venue was not verified; the PDF is a 2004 manuscript.
- Not consulted: Helson's book *Dirichlet Series* (2005), Queffélec–Queffélec, and Nikolski's "In a shadow of the RH" (Ann. Inst. Fourier 2012). Any of them might contain a Szegő-type statement for measures on a vertical line; none was found by search.
- I did not check whether Bostan–Chapoton (Exp. Math. 34 (2025) 384–403; title seen in Crossref) is related. It is probably about moment sequences given by Dirichlet series.

## 2. Extremal problems normalised at one coefficient or one value; mean values at zeros; lower bounds for Σ_ρ |P(ρ)|² h(γ)

### Takeaway
The closest extremal problem is Dimitrov–Oliveira's Problem 2, which is the dual of the user's problem:
- **Dimitrov–Oliveira:** minimise the flat-model norm ∫|B|² dt/(2π(1/4+t²)) over Dirichlet polynomials taking the value 1 at m fixed zeros. The minimum is the Christoffel-type quantity 1ᵀH⁻¹1 of the flat kernel at those zeros, asymptotic to (1/log n) Σ_{j≤m} 1/|ρ_j|² (unconditional).
- **The user:** minimise the zero-sampled norm Σ_ρ |P(ρ)|²/|ρ|² with the top coefficient fixed. The minimum stays ≥ d_1 (under RH) and grows like log k.

Mollifier problems at zeros normalise the k = 1 coefficient but optimise ratios involving ζ′(ρ). Fourier-optimisation methods (Beurling–Selberg-type extremal functions, reproducing kernels of de Branges spaces, semidefinite programming) solve extremal problems over sums at zeros or over pair correlation. None of them poses min Σ_ρ |P(ρ)|² w(ρ) with a coefficient normalisation.

### Cited Findings
- **Dimitrov–Oliveira, Problem 2** (full text).
  - "Let m ∈ ℕ, t_1, …, t_m be m distinct real numbers and D^p_{n,m}, m ≪ n, be the space of Dirichlet polynomials B_{n,p} of degree n which obey the m interpolation conditions B_{n,p}(1/p + it_j) = 1. Determine d²_{n,m,p} = inf (1/2π)∫|B_{n,p}(1/p+it)|² dt/(1/p² + t²)."
  - They motivate it by noting that every 1 − L(s,χ)A_n(s) "take[s] value one at the zeros".
  - Theorem 3: for n > n(m) the minimiser is unique and d²_{n,m,p} ∼ (1/log n) Σ_{j≤m} 1/(1/p² + t_j²).
  - The proof writes B = Σ b_k ψ_k, so the problem is to minimise ‖b‖² subject to Ab = 1_m. The minimum is 1*_m H⁻¹ 1_m with H = AA* = (K_n(t_i,t_j)), evaluated by Cramer's rule with (2.9)–(2.10).
  - For p = 2 at critical zeros, d²_{n,m,2} ∼ (1/log n) Σ_{j≤m} 1/|ρ_j|². They call "the similarity with the conditional result of Bettin, Conrey and Farmer … amazing".
  - — [arXiv:1608.07887](https://arxiv.org/abs/1608.07887).
- **Mean values at zeros.** Discrete mean values Σ_γ |A(ρ)|² and the Montgomery–Odlyzko/CGG ratio h(c) are documented in the earlier notes, as are the BFM Theorem 3.1 asymptotic and Milinovich–Ng's Möbius computation — [BFM, arXiv:2310.03949](https://arxiv.org/abs/2310.03949); [BMN, arXiv:0910.2052](https://arxiv.org/abs/0910.2052).
- **CGG 1998 "Simple zeros".** The mollifier is B(s) = Σ_{k≤y} μ(k) P(log(y/k)/log y) k^{−s}, so its k = 1 coefficient is P(1). The optimisation is over P in a ratio of mollified moments of ζ′(ρ) — [Bui–Heath-Brown, arXiv:1302.5018](https://arxiv.org/abs/1302.5018), as recorded in the earlier notes.
- **Carneiro–Chandee–Littmann–Milinovich**, Crelle 725 (2017) 143–182 (abstract).
  - Assuming RH, they bound Montgomery's N(T,β) "using Montgomery's formula and some extremal functions of exponential type". The functions "majorize and minorize the characteristic function of the interval [−β, β] in a way to minimize the L¹(ℝ, {1 − (sin πx/πx)²} dx)-error".
  - They give "a complete solution for this extremal problem using the framework of reproducing kernel Hilbert spaces of entire functions".
  - — [arXiv:1406.5462](https://arxiv.org/abs/1406.5462).
- **Carneiro–Chandee–Chirre–Milinovich** (abstract): under RH, they improve bounds for three integrals equivalent to the pair correlation conjecture "by introducing new connections to certain extremal problems in Fourier analysis" — [arXiv:2108.09258](https://arxiv.org/abs/2108.09258).
- **Carneiro–Milinovich–Soundararajan**, Comment. Math. Helv. 94 (2019) 533–568 (abstract): extremal problems in Fourier analysis improve the RH bound for the largest gap between consecutive primes — [arXiv:1708.04122](https://arxiv.org/abs/1708.04122).
- **Chirre–Gonçalves–de Laat** (abstract): semidefinite programming improves pair-correlation bounds "including the proportion of distinct zeros, counts of small gaps between zeros, and sums involving multiplicities of zeros" — [arXiv:1810.08843](https://arxiv.org/abs/1810.08843).
- **Targeted search with no hit.** arXiv abstracts with "Riemann hypothesis" + "Dirichlet polynomials" + "extremal" returned only Carneiro–Milinovich on Littlewood's bound for |ζ| on the critical line, which is unrelated — [arXiv:2403.17803](https://arxiv.org/abs/2403.17803).

### Inferences
- **Two dual problems with the same constant (computed here, from Dimitrov–Oliveira's formulas).**
  - Under RH, a Dirichlet polynomial P = Σ_{n≤k} x_n n^s can be measured in L²(flat), the Dimitrov–Oliveira and Lubinsky norm, or in L²(μ_Z), the user's norm.
  - Dimitrov–Oliveira fix values at zeros and minimise the flat norm. The minimum is governed by the flat Christoffel function Λ_n(ρ) = 1/K_n(γ,γ) ∼ 1/(|ρ|² log n) (their (2.9) at p = 2; written Λ_n to avoid a clash with Li's λ_n), and summing over finitely many zeros gives the BBLS/Burnol constant.
  - The user fixes the top coefficient and minimises the zero norm. The first pivot is the total mass d_1 = Σ_ρ 1/|ρ|².
  - The same constant 2 + γ − log 4π appears at both ends, in the opposite regime: (constant)/log n → 0 against ≥ constant.
- **No precedent for the coefficient-normalised problem.**
  - The mean-value literature evaluates Σ_ρ |A(ρ)|² for given coefficient families (Möbius, d_r, ζ-like).
  - The mollifier literature normalises the first coefficient inside ratios.
  - Neither minimises Σ_ρ |P(ρ)|² w(ρ) over all coefficient vectors with one fixed coefficient, as a function of the length.
- **Lineage of the method.** The user's proof (an archimedean minorant φλ − r certified pointwise, a Schur test, a sharp Mertens bound) belongs to the Beurling–Selberg/Fourier-optimisation family of these papers (CCLM, CMS, CGdL). Those papers optimise test functions for counting statistics of zeros or for pair correlation, not for pivots of a Dirichlet-polynomial Gram matrix.

### Gaps
- Not accessed: CGG 1998 itself, and Iwaniec–Luo–Sarnak's one-level-density extremal problems (Publ. IHES 2000). It is unverified whether any one-level density "uncertainty" bound is phrased with a coefficient normalisation of a Dirichlet polynomial.
- Not accessed: Montgomery–Odlyzko 1984, and how CGG 1984 normalises the coefficients.

## 3. Li's criterion: margin and monotonicity versions, and the role of λ_1 and Σ_ρ 1/|ρ|²

### Takeaway
Li's criterion has several known variants. Each characterises RH by a sign, a growth rate or an equality:
- a tolerance version: λ_n ≥ −C(ε)e^{εn} (Bombieri–Lagarias);
- a radius version: lim sup |λ_n|^{1/n} ≤ 1 (Lagarias);
- an asymptotic dichotomy (Voros);
- a mass identity: RH ⟺ Σ_ρ 1/|ρ|² = 2 + γ − log 4π (Gun–Murty–Rath, "easy to show");
- a monotonicity statement: under RH, λ_χ(n) increases in n for Dirichlet L-functions (Mazhouda, Monatsh. Math. 2013; abstract only). A conjecture that the λ_χ(n) are "positive and increasing" appears in a paper later retracted.

No source states "RH ⟺ λ_n ≥ λ_1 for all n" explicitly. It would follow from Li's criterion plus monotonicity under RH, if Mazhouda's theorem covers ζ.

Lagarias (2007, Thm 3.1) gives the full Gram matrix of Li's test functions under the Weil scalar product, ⟨G_n, G_m⟩ = λ_n + λ_m − λ_{n−m}. This is the exact "Li analogue" of the orbit Gram matrix. Its first pivot is again 2λ_1 = 2 + γ − log 4π. Unlike the orbit, its Gram–Schmidt pivots fall off a cliff (7.4·10⁻⁵ at k = 2, computed here). So the pivot margin is false in Li's basis and is not a general feature of Weil-type Gram matrices.

### Cited Findings
- **Li's criterion.** λ_n = Σ_ρ [1 − (1 − 1/ρ)^n], and RH ⟺ λ_n ≥ 0 for all n — [X.-J. Li, J. Number Theory 65 (1997) 325–333](https://doi.org/10.1006/jnth.1997.2137); bibliographic data verified via Crossref.
- **Lagarias, Thm 2.2** (full text). For an irreducible cuspidal unitary π on GL(n), each of the following is equivalent to RH for ξ(s,π):
  1. Re λ_n(π) ≥ 0 for all n ≥ 1;
  2. for each ε > 0 there is C(ε) > 0 with Re λ_n(π) ≥ −C(ε)e^{εn} for all n ≥ 1;
  3. lim sup |λ_n(π)|^{1/n} ≤ 1.
  - The equivalence of (1) and (2) "follows from the Corollary in Theorem 1 of [Bombieri–Lagarias]" — [Lagarias, "Li coefficients for automorphic L-functions", arXiv:math/0404394; Ann. Inst. Fourier 57 (2007) 1689–1740](https://arxiv.org/abs/math/0404394).
  - Bombieri–Lagarias is J. Number Theory 77 (1999) 274–287 — [DOI](https://doi.org/10.1006/jnth.1999.2392), verified via Crossref but not read; ScienceDirect returned 403.
- **Lagarias, Thm 3.1: the Weil scalar product on the Li class** (full text).
  - ⟨F, G⟩_W = Σ_ρ F(ρ)·conj(G(1 − ρ̄)), on the class L of rational functions vanishing at ∞ with poles only in {0, 1}.
  - For G_n(s) = 1 − (1 − 1/s)^n: "⟨G_n, G_m⟩_W(π) = λ_n(π) + λ_{−m}(π) − λ_{n−m}(π). In particular ‖G_n‖²_W = 2Re(λ_n(π))."
  - "The Li class L is large enough to characterize the Riemann hypothesis in terms of the semidefiniteness of the Weil scalar product."
  - "If the Riemann hypothesis holds, then the Weil scalar product is positive definite on L."
  - — [arXiv:math/0404394](https://arxiv.org/abs/math/0404394).
- **Lagarias, asymptotics** (full text). The archimedean part is S_∞(n,π) = (N/2) n log n + C_1(π) n + O(1), with C_1(π) = (N/2)(γ − 1 − log 2π) + (1/2) log Q(π). For π_triv, C_1 ≃ −1.1303307. Under RH the finite part is S_f(n,π) = O(√n log n) — [arXiv:math/0404394](https://arxiv.org/abs/math/0404394).
- **Voros** (full text). "Theorem (asymptotic criterion for the Riemann Hypothesis)":
  - RH true ⟺ λ_n ∼ (1/2) n(log n − 1 + γ − log 2π) (mod o(n));
  - RH false ⟺ "non-tempered oscillations" of exponentially growing amplitude.
  - Voros notes that Keiper had displayed this formula in a context suggesting it was "much stronger than" RH, and that Bombieri–Lagarias [2, Cor. 1(c)] showed "rather weak exponential lower bounds λ_n ≥ −ce^{εn}" imply RH.
  - — ["Sharpenings of Li's criterion for the Riemann Hypothesis", arXiv:math/0506326](https://arxiv.org/abs/math/0506326).
- **Maślanka** (abstract): over 3000 λ_n computed; the sequence "can be split into a strictly growing *trend* and some tiny *oscillations* superimposed on this trend" — [arXiv:math/0402168](https://arxiv.org/abs/math/0402168).
- **Mazhouda, "On the Li coefficients for the Dirichlet L-functions"**, Monatsh. Math. 170 (2013) 405–423 — [DOI](https://doi.org/10.1007/s00605-012-0436-3); bibliographic data verified via Crossref.
  - Abstract, as quoted in a search snippet of the Springer page: "we prove under the Riemann hypothesis that the Li coefficients for the Dirichlet L-functions λ_χ(n) are increasing in n. We also prove unconditionally that the first Li coefficients are increasing using the Bell polynomials."
  - The full text and abstract were not accessible: Springer redirected to a login, and Semantic Scholar marks the abstract "elided by the publisher".
- **Omar–Ouni–Mazhouda, "On the zeros of Dirichlet L-functions"** (arXiv full text).
  - Introduction: "Basing on the numerical computations made below, we conjecture that these coefficients are increasing in n. Should this conjecture hold, the validity of the Riemann hypothesis would follow."
  - §: "Conjecture. The coefficients λ_χ(n) are positive and increasing in n. This conjecture was partially numerical verified for the case of the Riemann zeta function."
  - Tabulated value: λ_χ(1) ≈ 0.0564 for χ mod 3.
  - — [arXiv:1507.03431](https://arxiv.org/abs/1507.03431).
  - **Caveat:** the journal version (LMS J. Comput. Math. 14 (2011) 140–154) "has been retracted … to prevent other authors from using incorrect mathematical results" — [retraction notice, LMS JCM 20 (2017) 53](https://doi.org/10.1112/S1461157018000013); [original record](https://doi.org/10.1112/s1461157010000215).
- **The Hecke case.** Omar–Ouni–Mazhouda, "On the Li coefficients for the Hecke L-functions", Math. Phys. Anal. Geom. 17 (2014) 67–81 — [DOI](https://doi.org/10.1007/s11040-014-9141-x). A search-engine summary claimed this paper states "RH holds iff the Li coefficients for Hecke L-functions increase with n". The MaRDI record has no abstract — [MaRDI](https://portal.mardi4nfdi.de/wiki/Publication:471812). **Unverified.**
- **Shifted, "modified" and τ-Li coefficients.**
  - Mazhouda: for F in the Selberg class and a < 1/2, RH ⟺ λ_F(n,a) = Σ_ρ [1 − ((ρ−a)/(ρ+a−1))^n] ≥ 0 for all n — [arXiv:1405.7354 (abstract)](https://arxiv.org/abs/1405.7354).
  - τ-Li coefficients give "a necessary and sufficient condition for the existence of zero-free strips" for automorphic L-functions — [Mazhouda, Rocky Mountain J. Math. 47 (2017) 1987–2011, abstract via Crossref](https://doi.org/10.1216/rmj-2017-47-6-1987).
- **The mass identity** (Gun–Murty–Rath, full text). "In this context, one has the following curious equivalence: Riemann hypothesis ⟺ Σ_ρ 1/|ρ|² = 2 + γ − log 4π. This is easy to show." The proof goes through Σ_ρ 1/ρ = Σ_ρ 2Re(ρ)/|ρ|². They also cite F. Brown, "Li's criterion and zero-free regions of L-functions", J. Number Theory 111 (2005) 1–32 — [arXiv:1807.11201](https://arxiv.org/abs/1807.11201); [Mathematika 64 (2018) 875–897](https://doi.org/10.1112/S0025579318000293).
  - A search-result summary says Elliott's survey also lists this equivalence (not read) — [arXiv:2407.17820](https://arxiv.org/abs/2407.17820).
- **Suzuki's screw function**, J. London Math. Soc. 108 (2023) 1448–1487 (full text) — [arXiv:2206.03682](https://arxiv.org/abs/2206.03682); [DOI](https://doi.org/10.1112/jlms.12785).
  - Ψ(t) = Σ_γ (1 − cos γt)/γ², with γ the zeros of ξ(1/2 − iz) (Thm 1.1(2)); it is defined unconditionally from the primes in (1.1).
  - g = −Ψ, and G_g(t,u) = g(t−u) − g(t) − g(−u) + g(0) = Σ_γ (e^{iγt} − 1)(e^{−iγu} − 1)/γ² (eq. 1.9).
  - Thm 1.2: RH ⟺ g is a screw function, i.e. G_g is non-negative definite on ℝ.
  - Thm 1.3: RH ⟺ ⟨φ, φ⟩_{G_g,a} ≥ 0 on C_0(a) for all a, an analogue of Weil's criterion. Under RH the form is positive definite on L²(−a, a).
  - Thm 1.4: RH ⟺ non-degeneracy on L²(−a, a) for all a, an analogue of Yoshida's criterion.
  - Thm 1.6: RH ⟺ Ψ = O(1).
  - Thm 1.7: RH ⟺ Ψ ≥ 0 pointwise; under RH, Ψ(t) > 0 for t ≠ 0.
  - Thm 1.8: RH ⟺ the Hankel determinants of the moments µ_n = ∫_0^∞ 4^{−1} e^{−t/2} Ψ(t) tⁿ dt are ≥ 0.
  - Suzuki: "Bombieri–Lagarias found that the positivity of all Li coefficients is a discretization of the positivity of the Weil distribution."
  - Extension: for the extended Selberg class, "the Grand Riemann Hypothesis … is equivalent to the nonpositivity of the corresponding screw function" — [Suzuki, IJNT 21 (2025) 1815–1823, arXiv:2209.12832 (abstract)](https://arxiv.org/abs/2209.12832).
  - Further: "Li coefficients as norms of functions in a model space" — [arXiv:2301.05779 (abstract)](https://arxiv.org/abs/2301.05779).
- **The repository's own statements.**
  - d_1 = K_H(1) = 2 + γ − log 4π.
  - RH ⟺ the orbit Gram matrix with Hadamard weights is positive definite (`BallHadamard.rh_iff_posDefH`).
  - The margin version, `PivotSharp.rh_iff_orbitLattice`.
  - — [docs/ball-conjecture.md](../../docs/ball-conjecture.md), lines 18–25 and 185.

### Inferences
- **d_1 is the first Li coefficient, doubled, unconditionally (computed here).**
  - 1/(ρ(1−ρ)) = 1/ρ + 1/(1−ρ), and the zero multiset is symmetric under ρ ↦ 1 − ρ, so K_H(1) = 2 Σ_ρ 1/ρ = 2λ_1.
  - Numerically (mpmath, 60 digits, from λ_n = (1/(n−1)!) dⁿ/dsⁿ[s^{n−1} log ξ(s)] at s = 1): λ_1 = 0.023095708966121, and 2λ_1 = 0.0461914179322421 = 2 + γ − log 4π to all printed digits.
  - So the orbit's d_1, Lagarias's ‖G_1‖²_W = 2λ_1 (Thm 3.1, n = 1), the BBLS/Burnol/BCF constant, and Gun–Murty–Rath's mass are one number. Under RH it is the total mass of μ_Z.
- **The Li orbit is the circle analogue of the user's orbit, and its pivots collapse (computed here).**
  - Under RH, z_ρ = 1 − 1/ρ lies on the unit circle and G_n − G_{n−1} = z^{n−1}/s. Hence span{G_1, …, G_n} = (1/s)·{polynomials of degree < n in z}.
  - Lagarias's Gram matrix (λ_n + λ_m − λ_{n−m}) therefore has as its Gram–Schmidt pivots the monic norms ‖Φ_{k−1}‖² of orthogonal polynomials on the unit circle (OPUC) for μ = Σ_ρ |ρ|^{−2} δ_{z_ρ}. (Its Toeplitz form in the increment basis, (λ_{j−k+1} − 2λ_{j−k} + λ_{j−k−1}), is the matrix derived in the earlier notes. That matrix is thus a change of basis of Lagarias's Thm 3.1, not new.)
  - These pivots are non-increasing, since zΦ_n is a monic competitor of the same norm. By the Szegő–Kolmogorov theorem (standard; not re-verified here) they tend to 0 because μ has no absolutely continuous part.
  - **Values** (computed from λ_1, …, λ_8):
    - λ_2 = 0.0923457352280, λ_3 = 0.2076389205543, λ_4 = 0.3687904794922.
    - Pivots: 0.0461914, 7.42·10⁻⁵, 1.68·10⁻⁷, 2.07·10⁻¹⁰, 2.22·10⁻¹³, 1.61·10⁻¹⁶, 1.08·10⁻¹⁹, 5.89·10⁻²³.
    - pivot_2/pivot_1 = 0.0016. The decay rate, about 10⁻³ per step, is consistent with the capacity of the arc carrying μ: sin²(θ_1/2) ≈ 1.25·10⁻³, where θ_1 = arg(1 − 1/ρ_1) ≈ 0.0707.
  - The orbit pivots instead satisfy d_2 = 1.718·d_1 and grow like log k under RH.
- **Same measure, same first vector, same flat model, opposite behaviour (computed here).**
  - The Cayley map s ↦ z = 1 − 1/s sends the critical line to the unit circle and dt/(2π(1/4+t²)) to dθ/2π, since |dz| = dt/|s|².
  - The flat model is therefore normalised Lebesgue measure on the circle in Li's coordinate (OPUC zⁿ, every pivot 1), and min(m,n) in the user's coordinate (every pivot 1).
  - With the zeros in place of the flat measure:
    - the shift orbit zⁿ (Li/Lagarias) has pivots decreasing to 0;
    - the dilation orbit n^s (the user's) has pivots increasing like log k.
  - The margin "pivot_k ≥ pivot_1" is thus not a consequence of Weil positivity in general. It is particular to the multiplicative orbit.
- **The diagonal is trivial in the orbit; the content is in the Schur complements.**
  - Li-type margins ("λ_n ≥ λ_1", monotonicity) are diagonal statements, ‖G_n‖² ≥ ‖G_1‖².
  - In the orbit, ‖w_k‖² = k·d_1 holds unconditionally (diagonal Gram entry √(k·k)·K_H(1)). The diagonal margin is automatic, and the whole content of d_k ≥ d_1 lies in the off-diagonal (Schur-complement) structure.
  - So the user's statement is not a rephrasing of any Li-type monotonicity.
- **Relation to Suzuki.**
  - The orbit Gram matrix is diag(√n)·[K(log m − log n)]·diag(√n), with K(τ) = Σ_γ e^{iγτ}/(1/4+γ²) under RH: a stationary kernel sampled at log n.
  - Suzuki's kernel is a stationary-increments (screw) kernel with weights 1/γ², over all t ∈ ℝ.
  - Both express RH as the positivity of a translation-structured kernel built from the explicit formula. Neither Suzuki's paper nor Lagarias's states any margin or pivot bound.

### Gaps
- Mazhouda (Monatsh. 2013) could not be read. I could not check whether "Dirichlet L-functions" includes ζ (the principal character mod 1), what explicit constants are used, or whether the proof is sound. A related LMS JCM paper by the same group was retracted for "incorrect mathematical results". The Hecke paper's claimed "RH ⟺ increasing" is unverified.
- Not read: Bombieri–Lagarias 1999, Keiper 1992 and Brown 2005; they are used only as restated.
- No source explicitly states "RH ⟺ λ_n ≥ λ_1 for all n", or a Gram–Schmidt (pivot) version of Li's criterion.
- Broughan's *Equivalents of the Riemann Hypothesis* (CUP 2017) was not accessible. It may list the Σ1/|ρ|² identity and monotonicity results; this was not checked.

## 4. Distance criteria with distances bounded below; RH as a uniform lower bound on distances from spans

### Takeaway
Distance lower bounds in the NB setting are unconditional asymptotic statements and do not characterise RH:
- lim inf d_N² log N ≥ Σ m_ρ²/|ρ|² (BBLS; Burnol 2002; de Roton for the Selberg class);
- the conjectured equality d_N² ∼ (2 + γ − log 4π)/log N would imply RH and simple zeros (BBLS, as reported by Balazard–de Roton; BCF prove it conditionally).

Two unconditional results give positive but non-uniform distances: Vasyunin's minimality of the Báez-Duarte system, and the complete biorthogonal sequence of Calderaro–Manzur–Noor–Santos. In Suzuki's screw-function framework, RH is equivalent to non-degeneracy (no zero eigenvalue), not to a uniform bound. No criterion of the form "RH ⟺ every Gram–Schmidt distance in a natural sequence is ≥ a fixed explicit constant" was found, apart from the user's.

### Cited Findings
- **Burnol and BBLS.**
  - Burnol, Thm 1.3: lim inf_{λ→0} D(λ)√(log 1/λ) ≥ √(Σ_ρ m_ρ²/|ρ|²) — [Burnol, arXiv:math/0103058](https://arxiv.org/abs/math/0103058).
  - BBLS conjectured equality; Balazard–de Roton note this would imply RH and simple zeros — [arXiv:0812.1689](https://arxiv.org/abs/0812.1689).
  - BCF prove d_N² log N → 2 + γ − log 4π under RH and Σ_{|γ|≤T} 1/|ζ′(ρ)|² ≪ T^{3/2−δ} — [arXiv:1211.5191](https://arxiv.org/abs/1211.5191).
  - All of these are documented in the earlier gram_and_nyman_beurling notes.
- **Vasyunin and the biorthogonal question** (full text, introduction).
  - "Vasyunin showed in [22] that the Báez-Duarte sequence {ρ_{1/k} : k ≥ 2} is minimal by constructing a biorthogonal sequence for it in L²(0, 1)."
  - "the completeness of (h_k)_{k≥2} in H² is equivalent to the RH by Theorem 1."
  - Their Theorem 15 shows "(h_k)_{k≥2} possesses a complete biorthogonal sequence in H²".
  - Minimality means e_n ∉ closed span(e_k)_{k≠n} for each n (their Prop. 8, citing a standard lemma).
  - They also relate "the size and dimension of N^⊥" to the zeros, and give "a new approach for finding zero-free half-planes".
  - — [Calderaro–Manzur–Noor–Santos, "Orthogonality questions in the Hardy space related to ζ-zeros", arXiv:2203.05030](https://arxiv.org/abs/2203.05030).
  - Vasyunin's paper is "On a biorthogonal system associated with the Riemann hypothesis", Algebra i Analiz 7:3 (1995) 118–135; St. Petersburg Math. J. 7:3 (1996) 405–419 — [Math-Net.ru](https://www.mathnet.ru/eng/aa557).
- **Vasyunin's cotangent-sum asymptotic.** Pyvovarov quotes (π/n) Σ_{k=1}^{n−1} (1/2 − k/n) cot(πk/n) = log n + γ − log 2π + O(1/n). Vasyunin's formula expresses the NB norms as arithmetic cotangent sums — [Pyvovarov, arXiv:2607.12084 (2026 preprint)](https://arxiv.org/abs/2607.12084).
- **Suzuki, Thm 1.4** (full text): RH ⟺ the screw-kernel form is non-degenerate on L²(−a, a) for every a, i.e. G_g[a] has no zero eigenvalue. Section 4 states "a lower bound for ⟨φ, φ⟩_{G_g,a} under restrictions to φ" for small a — [arXiv:2206.03682](https://arxiv.org/abs/2206.03682).
- **Nikolski 1995 and Burnol 2004.**
  - Nikolski: "a subspace of a holomorphic Hilbert space is completely determined by their distances to the reproducing kernels", with zero-free discs for ζ — [Numdam](https://www.numdam.org/item/AIF_1995__45_1_143_0/).
  - Burnol: in which Sonine spaces the zeros give complete or minimal systems — [Numdam](https://www.numdam.org/item/JTNB_2004__16_1_65_0/).
  - Both are as in the earlier notes (abstracts).
- **Dimitrov–Oliveira's unconditional asymptotic** d²_{n,m,2} ∼ (1/log n) Σ_{j≤m} 1/|ρ_j|² (Section 2 above) — [arXiv:1608.07887](https://arxiv.org/abs/1608.07887).

### Inferences
- **NB and the orbit use complementary measures (derived here).**
  - The NB approximants ζ(s)k^{−s} have, in L²(dt/(2π|s|²)), the Gram matrix of k^{−s} for the measure |ζ(1/2+it)|² dt/(2π(1/4+t²)). That measure vanishes at the zeros.
  - The orbit uses the measure μ_Z, which is concentrated on the zeros.
  - In NB the distance of the target tends to 0 (iff RH). In the orbit every pivot stays ≥ d_1 (iff RH).
  - The constant Σ1/|ρ|² enters NB through flat-model Christoffel functions at the zeros (Burnol; Dimitrov–Oliveira), and enters the orbit as the mass of μ_Z.
- **Minimality is not a margin.** Vasyunin's and Calderaro et al.'s results are non-uniform (each distance positive). Suzuki's Thm 1.4 is a non-degeneracy statement. None asserts a uniform explicit lower bound equivalent to RH.

### Gaps
- Vasyunin's paper, Landreau–Richard's NB numerics (Exp. Math. 2002) and BBLS 2005 were not read. They may contain observations on Gram–Schmidt distances of the NB system.
- The lower bound in Suzuki's §4 was not extracted in detail.

## 5. Zeta-specificity: do margin or positivity criteria stronger than RH hold for ζ but fail for L-functions or function fields?

### Takeaway
The clearest precedent is Conrey–Li (1998/2000). De Branges's positivity conditions imply GRH, but they are false for the de Branges spaces of ζ and of L(s,χ_4). That positivity condition, stronger than RH, fails for ζ itself.

I found no source in which a margin criterion is equivalent to RH for ζ yet fails for some Dirichlet L-function or curve. The only such observations are the repository's own tests:
- the margin d_2 < d_1 fails for 5983 of 29468 primitive characters with q ≤ 400;
- it fails for 98 of 148 curves.

For function fields, Li's (non-margin) criterion has been established (Omar–Bouanani, titles only).

### Cited Findings
- **Conrey–Li** (full text) — [arXiv:math/9812166](https://arxiv.org/abs/math/9812166).
  - "We shall give examples showing that de Branges' positivity conditions, which imply the generalized Riemann hypothesis, are not satisfied by defining functions of reproducing kernel Hilbert spaces associated with the Riemann zeta function ζ(s) and the Dirichlet L-function L(s, χ4)."
  - **Theorem 1 (de Branges).** Assume E has no real zeros, |E(z̄)| < |E(z)| on Im z > 0, Ē(z̄) = εE(z − i), and |E(x+iy)| strictly increases in y > 0. If Re⟨F(z), F(z+i)⟩_{H(E)} ≥ 0 for all admissible F, then the zeros of E lie on Im z = −1/2 and Re{Ē′(w)E(w+i)/2πi} ≥ 0 at its zeros.
  - **ζ:** they conclude "the Hilbert space of entire functions H(E) with E(z) = ξ(1 − iz) does not satisfy the condition (3.1)". The same holds for the space F(W) with W = 1/ξ(1 − iz) and condition (3.3).
  - **L(s,χ_4):** at ρ = 1/2 + i·67.6369208635…, −Re{ξ′(ρ,χ_4)ξ(1+ρ,χ_4)} = −2.310349… × 10⁻⁴⁵ < 0.
  - The journal venue (IMRN 2000, no. 18) comes from search summaries — [Wikipedia, de Branges](https://en.wikipedia.org/wiki/Louis_de_Branges_de_Bourcia).
- **Function fields** (titles and bibliographic data only, via Crossref).
  - Omar–Bouanani, "Li's criterion and the Riemann hypothesis for function fields", Finite Fields Appl. 16 (2010) 477–485 — [DOI](https://doi.org/10.1016/j.ffa.2010.09.004).
  - Part II, Finite Fields Appl. 45 (2017) 53–58 — [DOI](https://doi.org/10.1016/j.ffa.2016.11.010).
- **Sensitivity of Weil positivity to the primes.** Connes–Consani found that requiring positivity pins p to an interval of size ~10⁻³ around 2. They also found that the archimedean place alone "ceases to be positive in the upper part of the interval log(λ²) ∈ [log 2 − 0.2, log 2 + 0.2]". This is documented in the earlier notes — [arXiv:2106.01715](https://arxiv.org/abs/2106.01715).
- **Repository tests.** The margin fails for curves over finite fields (98 of 148 have some d_k < d_1 with k ≤ 150), and for 5983 of 29468 primitive characters with q ≤ 400 (d_2 < d_1). For quadratic characters a positive proportion fails, by a random model — [docs/ball-conjecture.md](../../docs/ball-conjecture.md), lines 194–220.

### Inferences
- There are two kinds of statement stronger-looking than RH:
  - **De Branges type:** positivity of a shifted form. It is sufficient for RH but false for ζ (Conrey–Li).
  - **The orbit margin:** under RH, it is a consequence of RH for ζ and hence equivalent to it, but it is not structural; it fails for L(s,χ) and for curves.
- Among the sources found here, the orbit margin is the only explicit example of a margin inequality equivalent to RH for ζ alone whose natural analogues fail for other L-functions where GRH is expected. It shows the margin comes from ζ's numerical data (conductor 1, K_H(1) = 0.046, no zero below 14.13), as the repository's docs say.
- The Li orbit shows the margin also depends on the choice of orbit: with the same zeros the margin fails at k = 2 (Section 3).

### Gaps
- Not checked: whether Li coefficients λ_n(χ) are monotone, or satisfy λ_n(χ) ≥ λ_1(χ), for all characters. This is the diagonal analogue of the repository's d_2 < d_1 test, and Mazhouda's claimed theorem would cover it under GRH.
- The Omar–Bouanani papers were not read.

## 6. Verdict: is the extremal/margin equivalence, or a close variant, in the literature?

### Takeaway
**No.** I found no statement, in this form or a close variant, that among Dirichlet polynomials Σ_{n≤k} x_n n^s with x_k = 1 the zero-weighted mean square Σ_ρ |P(ρ)|²/|ρ|² is minimised by P = 1 for every k, and that this is equivalent to RH. I also found none of the following:
- that the monic orthogonal Dirichlet polynomials for Σ_ρ δ_ρ/|ρ|² never have norm below the first;
- that the Gram–Schmidt pivots of any explicit-formula Gram matrix are bounded below by the first pivot;
- the RH bound ≥ 0.0577 and the log k growth of these minima.

The repository's own October and November 2026 searches reached the same conclusion — [docs/ball-conjecture.md](../../docs/ball-conjecture.md), line 225.

The closest results, in order of closeness:
1. **Lubinsky (2014) and Dimitrov–Oliveira (2016).** Orthogonal Dirichlet polynomials for the flat weight, which give the flat model's min(m,n) Gram matrix and constant pivots. Dimitrov–Oliveira's dual extremal problem (flat norm, value 1 at zeros) has the minimum ∼ (1/log n) Σ 1/|ρ_j|².
2. **Lagarias (2007), Thm 3.1.** The Gram matrix λ_n + λ_m − λ_{n−m} of Li's test functions under the Weil scalar product: RH ⟺ semidefiniteness, and its first pivot is 2λ_1 = 2 + γ − log 4π. Its pivots collapse, so its margin version is false.
3. **Suzuki (2023, JLMS), screw-function criteria.** RH ⟺ positivity or non-degeneracy of a stationary-type kernel built from the zeros/primes; no margin.
4. **Gun–Murty–Rath (2018).** RH ⟺ Σ_ρ 1/|ρ|² = 2 + γ − log 4π. This is exactly "d_1 is the total mass of μ_Z".
5. **Mazhouda (2013) and Omar–Ouni–Mazhouda.** Li coefficients increasing in n under RH (Dirichlet L-functions; abstract only), and conjectured "positive and increasing" (retracted paper). This is a diagonal margin of Li type.
6. **BBLS/Burnol/BCF.** The same constant as the asymptotic NB distance; unconditional lower bounds; equality conjectured.
7. **Bombieri–Lagarias / Lagarias Thm 2.2 / Voros.** Tolerance, radius and asymptotic versions of Li's criterion.
8. **Conrey–Li (2000).** A positivity condition stronger than RH (de Branges) that fails for ζ and L(s,χ_4).

### Cited Findings
- Lubinsky — [DOI](https://doi.org/10.1016/j.jat.2013.10.001); Dimitrov–Oliveira — [arXiv:1608.07887](https://arxiv.org/abs/1608.07887).
- Lagarias — [arXiv:math/0404394](https://arxiv.org/abs/math/0404394).
- Suzuki — [arXiv:2206.03682](https://arxiv.org/abs/2206.03682).
- Gun–Murty–Rath — [arXiv:1807.11201](https://arxiv.org/abs/1807.11201).
- Mazhouda — [DOI](https://doi.org/10.1007/s00605-012-0436-3); Omar–Ouni–Mazhouda — [arXiv:1507.03431](https://arxiv.org/abs/1507.03431).
- Burnol — [arXiv:math/0103058](https://arxiv.org/abs/math/0103058); BCF — [arXiv:1211.5191](https://arxiv.org/abs/1211.5191).
- Voros — [arXiv:math/0506326](https://arxiv.org/abs/math/0506326); Conrey–Li — [arXiv:math/9812166](https://arxiv.org/abs/math/9812166).

### Inferences
- **What to credit.**
  - The flat-model computation: Lubinsky (2014), and Dimitrov–Oliveira for the explicit p = 2 form.
  - "d_1 = 2λ_1 = 2 + γ − log 4π, the mass of μ_Z iff RH": Li/Keiper for λ_1, and Gun–Murty–Rath for the equivalence.
  - PSD-type equivalences of RH via explicit-formula Gram kernels: Weil, Lagarias Thm 3.1 and Suzuki.
- **What appears new.**
  - The margin form (pivots ≥ first pivot, equivalently w_1 a shortest vector of the orbit lattice) and its equivalence with RH.
  - The explicit RH bound d_k ≥ 0.0577 for k ≥ 2.
  - The log k growth of the minima.
  - The contrast with the Li orbit, whose pivots collapse (7.4·10⁻⁵ at k = 2) under the same zeros and the same flat model.
- **Phrasing for a write-up.** Present it as "a margin version of a Weil-type positivity criterion that is special to the multiplicative orbit and to ζ", not as "the first extremal problem at zeros". Dimitrov–Oliveira already posed and solved an extremal problem at zeros, of dual type.

### Gaps
- Not queried: MathSciNet, zbMATH (403 to WebFetch), Google Scholar citation trails of Li 1997 and Bombieri–Lagarias 1999, and Broughan's book. A statement in a conference proceedings or a thesis could have been missed.
- Not read, for access reasons: Lubinsky's papers, Mazhouda's Monatshefte paper, the Omar–Ouni–Mazhouda Hecke paper, Bombieri–Lagarias 1999, Keiper 1992, Brown 2005, Vasyunin 1996 and Iwaniec–Luo–Sarnak 2000.
