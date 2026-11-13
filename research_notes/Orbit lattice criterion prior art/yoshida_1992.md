# Yoshida 1992, "On Hermitian forms attached to zeta functions": full-text check against the orbit criteria (A) and (B)

**Source.** H. Yoshida, "On Hermitian forms attached to zeta functions", *Zeta Functions in Geometry*, Advanced Studies in Pure Mathematics 21 (1992), pp. 281–325 (received September 3, 1990).

**Full text** — the 45-page scan uploaded by the user, read in full. It is an image scan with an OCR layer.
- All page numbers below are the **journal's**; PDF page = journal page − 280.
- I transcribed the formulas from 170-dpi renders of the pages.

**Relation to earlier notes.** This note supersedes Q1 of `weil_form_subspaces_and_lattices.md`, which relied only on second-hand accounts (Bombieri 2000, Suzuki 2023, Connes, zbMATH), and closes the gaps listed there.

**Claims under test** (as in the earlier notes):
- **(A)** RH ⟺ every Gram–Schmidt pivot d_k of the orbit vectors w_1, w_2, … satisfies d_k ≥ d_1 = K_H(1) = 2 + γ − log 4π ≈ 0.0462. Under RH, d_k ≥ 0.0577 ≈ 1.249·d_1 for k ≥ 2, and d_k ≫ log k.
- **(B)** RH ⟺ for every N, every nonzero integer vector a has Q_N(a) ≥ K_H(1); that is, w_1 is a shortest vector of the orbit lattice.
- Here G_N = (√(mn)·K_H(m/n))_{m,n≤N} and K_H(r) = Σ_ρ r^{ρ−1/2}/(ρ(1−ρ)).

**Source tags.**
- "(p. N)": quoted or closely paraphrased from journal page N.
- "(computed here)": my own computation in this session.
- "Inference": my reasoning, not in the paper.

---

## Verdict

**Yoshida 1992 contains neither (A) nor (B), nor a close variant.**

**What the paper does not contain.**
- No RH-equivalent is phrased through Gram–Schmidt pivots, determinants, eigenvalues, lattices, integer vectors or shortest vectors.
- No lower bound is ever measured against a first vector or a first term. Every margin in the paper is relative to ‖φ‖²_{L²}.
- The repository's test vectors never appear:
  - the step functions 1_{(0,n]};
  - their Mellin transforms n^s/s, i.e. Dirichlet polynomials;
  - translates by log n used as test vectors.

  All of Yoshida's test functions are compactly supported in the log variable and have entire Mellin transforms (p. 283).
- The repository's comparison vector w_1 lies outside every space Yoshida considers.

**Closest statements, in decreasing order of structural similarity to (A).**
1. **Lemma 9 and §7 (pp. 312–319): Gram–Schmidt and Cholesky for the Weil form.**
   - Yoshida applies "the Schmidt orthogonalization process" (7.6) to the high Fourier modes η_k of a window. He factors their Weil Gram matrix as C ᵗC̄ with C lower triangular (7.8), and bounds ‖X_1^{−1}‖ ≤ κ_1^{−1} (7.19) and ‖X_4^{−1}‖ ≤ (µ(M) − κ_1^{−1}ν)^{−1} (7.23).
   - *Unstated consequence* (inference): every Gram–Schmidt pivot of these modes is ≥ κ_1², and the pivots of index > M are ≥ (µ(M) − κ_1^{−1}ν)² → ∞. This is the paper's only instance of "each new vector keeps a distance from the span of the previous ones".
   - It differs from (A) in four ways:
     - it is unconditional;
     - it follows trivially from an assumed coercivity bound (hypothesis (I));
     - it concerns the high-frequency modes of a single window;
     - it serves only to prove that the form on the finite block W(a) varies continuously with a.
2. **The finite-section remark after (5.18) (p. 302).** "If R.H. holds, the finite dimensional matrix ((⟨χ_n, χ_m⟩) | |n|, |m| ≤ N) must be positive definite for every N and a."
   - Only this direction is stated.
   - In pivot language this says "all pivots > 0", for the Fourier modes of every window. (A) says "all pivots ≥ d_1", for the multiplicative orbit.
3. **The §6 certification of Theorem 1 (pp. 306–310).** Positivity at a = (log 2)/2, k = ℚ, is proved by certified Gaussian elimination:
   - leading principal minors det(u_ij; 1 ≤ i, j ≤ k) > 0 for k ≤ 10 (odd part);
   - interval lower bounds on the final diagonal entries of a 200 × 200 matrix (even part).

   Only positivity is checked, and no pivot values are reported.
4. **L²-margins.**
   - Lemma 3 (p. 290): ⟨φ, φ⟩ ≥ µ‖φ‖²_{L²} on K_N(a), for any µ, uniformly in 0 < a ≤ a_0.
   - (6.8)–(6.9) (p. 305): the same bound with explicit constants 1.52 and 4.08.
   - The proof of Lemma 2 (p. 289): a margin on whole small windows.

   All three are unconditional and live on high-mode subspaces or small windows.
5. **RH-equivalences** (none of them a margin statement):
   - Theorem 2 (p. 321): RH ⟺ non-degeneracy on K̂(a) for every a;
   - Proposition 1 (p. 285): odd test functions suffice;
   - the introduction (p. 281): RH ⟺ positive definiteness on C(a) for every a;
   - Proposition 6 (p. 320): a critical window a_0 exists if RH fails.

**For (B):** nothing comparable. Integers enter only as Fourier indices and in the unique-factorisation step of Proposition 7's proof (pp. 323–324).

### Suggested citation sentences
- "Yoshida [Y92] localised Weil's criterion to test functions supported in a window [−a, a] of the logarithmic variable. He showed that RH for a Dedekind zeta function is equivalent to the non-degeneracy of Weil's hermitian form on a completed space K̂(a) for every a > 0 [Y92, Thm. 2]. He also showed that on the high Fourier modes of a window the form dominates any prescribed multiple of the L²-norm [Y92, Lemma 3]. For a = (log 2)/2 he verified positivity by a certified Gaussian elimination of a finite Gram matrix of trigonometric modes [Y92, Thm. 1, §6]."
- "Unlike [Y92], whose test functions are compactly supported and whose positivity bounds are relative to the L²-norm, our test vectors are the multiplicative translates 1_{(0,n]} (equivalently, Dirichlet polynomials), which lie in no window. Our criteria bound every Gram–Schmidt pivot below by the first one (resp. identify w_1 as a shortest vector of the integer orbit lattice). No statement of this kind appears in [Y92]."

---

## Dictionary: Yoshida's set-up versus the repository's

- **Yoshida's form.**
  - Yoshida's x is the logarithmic variable.
  - Mellin transform: M(α)(s) = ∫ α(x) e^{(s−1/2)x} dx (p. 283).
  - The form: ⟨φ_1, φ_2⟩ = T_k(φ_1 ∗ φ̃_2), where φ̃(x) = \overline{φ(−x)} and T_k(F) = lim_{T→∞} Σ_{|Im ρ|<T} M(F)(ρ) (pp. 281, 284, 287).
  - Under RH, ⟨φ, φ⟩ = Σ_ρ |M(φ)(ρ)|² (p. 286; used again on p. 321).
- **The orbit vectors in Yoshida's notation (computed here).**
  - Put φ_n(x) = e^{x/2}·1_{(−∞, log n]}(x) = √n·φ_1(x − log n).
  - Then M(φ_n)(s) = n^s/s for Re s > 0. With T defined by the zero sum, ⟨φ_m, φ_n⟩ = Σ_ρ m^ρ n^{1−ρ}/(ρ(1−ρ)) = √(mn)·K_H(m/n).
  - So G_N is exactly the Gram matrix of Yoshida's hermitian form on φ_1, …, φ_N, and the w_n are these φ_n.
  - The form is translation invariant: T((τ_hφ) ∗ (τ_hψ)~) = T(φ ∗ ψ̃). This is why G_N depends only on m/n, up to the √(mn) weights.
- **Where the orbit vectors sit relative to Yoshida's spaces.**
  - φ_n is not compactly supported, and φ_1 ∗ φ̃_1 = e^{−|x|/2} has Mellin transform 1/(s(1−s)), with poles at 0 and 1 (computed here). So φ_n lies outside C(a), K(a) and K̂(a), all of whose elements have entire Mellin transforms.
  - The prime side of the explicit formula diverges for e^{−|x|/2} (Σ Λ(n)/n). This is why K_H must be evaluated by a regularised explicit formula.
  - *Inference.* A combination Σ x_n φ_n with Σ x_n = 0 (i.e. P(0) = 0 for P(s) = Σ x_n n^s) is supported in [0, log N]. Translated by −(log N)/2, it is a step-type function in L²[−a, a] with a = (log N)/2. Its Fourier coefficients are O(1/|n|), so by (5.17)–(5.18) its Weil norm is finite and it lies in K̂(a).
  - Hence Yoshida's framework sees only the hyperplane Σ x_n = 0 of span(w_1, …, w_N). It never sees w_1 itself, nor any vector with Σ x_n ≠ 0.
- **Dilations, not translates.** Yoshida moves between windows by the dilations α_t(x) = t^{−1}α(t^{−1}x) (§7, p. 311). He never uses translates by log n as test vectors.
- **Normalisation check (computed here).** Take k = ℚ, a = (log 2)/2 and χ_0 = (2a)^{−1/2}·1_{[−a,a]}, the L²-normalised indicator of the window.

  | Evaluation of ⟨χ_0, χ_0⟩ | Value |
  |---|---|
  | Yoshida's closed formula (5.15) at n = 0 | 0.183383 |
  | Its archimedean part, by numerical integration of the explicit formula on p. 281 | agrees to 3·10⁻⁷ |
  | Zero sum Σ_γ (2/a) sin²(aγ)/γ² over the first 600 zeros, plus a density tail | 0.183388 |

  - The density tail must include the resonance with the prime 2, since 2a = log 2. Its contribution is √2/(πT) ≈ 4.8·10⁻⁴.
  - So my transcription of (5.15) is right. Yoshida's ⟨·,·⟩ is the same functional as the repository's, with the same normalisation; for comparison, K_H(1) = 0.046191 for the L²-normalised φ_1.

---

## Q1. Definitions, main results and RH-equivalences (exact statements)

### Definitions
- **Explicit formula and the form** (p. 281).
  - "For F ∈ C_c^∞(**R**), set Φ(s) = ∫_{−∞}^{∞} F(x)e^{(s−1/2)x} dx, s ∈ **C**, F̂(t) = Φ(1/2 + it), t ∈ **R**."
  - The explicit formula for ζ: Σ_ρ Φ(ρ) = ∫F(x)(e^{x/2} + e^{−x/2})dx − (log π)F(0) − Σ_p Σ_{m≥1} (log p/p^{m/2})(F(m log p) + F(−m log p)) + (1/2π)∫F̂(t) Re ψ(1/4 + it/2) dt.
  - "The functional T(F) = Σ_ρ Φ(ρ) defines a distribution on **R**. A well known observation of Weil states that T is positive definite i.e. T(α ∗ α̃) ≥ 0 for every α ∈ C_c^∞(**R**) if and only if the Riemann hypothesis holds for ζ(s). We can define a hermitian form ⟨ , ⟩ on C_c^∞(**R**) by ⟨φ_1, φ_2⟩ = T(φ_1 ∗ φ̃_2)."
- **Mellin transform and admissible functions** (p. 283).
  - α̌(x) = α(−x), α̃(x) = \overline{α(−x)}.
  - "If α is an integrable function with compact support, we define its Mellin transform M(α) by M(α)(s) = ∫ α(x)e^{(s−1/2)x} dx … We see that M(α) is an entire funcion [sic]."
  - (1.1) M(α̌)(s) = M(α)(1−s); (1.2) M(α̃)(s) = \overline{M(α)(1−s̄)}; (1.3) M(α ∗ β) = M(α)M(β).
  - "Let F be a continuous function with compact support which is continuously differentiable except for a finite number of points. For discontinuous points of F′, we assume the existence of right and left limits of F′. In this paper, we call such F *admissible*."
- **Number fields** (p. 284).
  - (1.6) is the explicit formula for the Dedekind zeta function ζ_k(s), with A_k = π^{−r_1}(2π)^{−2r_2}|D_k|.
  - Its archimedean terms are r_1V_1(F) + 2r_2V_2(F), where V_1 uses Re ψ(1/4 + it/2) and V_2 uses Re ψ(1/2 + it).
  - T_k(F) = lim_{T→+∞} Σ_{|Im ρ|<T} Φ(ρ).
- **Positive definiteness** (pp. 284–285). "T is called positive definite if T(α ∗ α̃) ≥ 0 for every α ∈ C_c^∞(**R**). We call T evenly (resp. oddly) positive definite if T(α ∗ α̃) ≥ 0 for every even (resp. odd) function α ∈ C_c^∞(**R**)."
- **The spaces C(a) and K(a)** (p. 287; also pp. 281–282).
  - "C(a) = { φ ∈ C_c^∞(**R**) | supp(φ) ⊆ [−a, a] }."
  - "K(a) = { φ | there exists f ∈ C^∞(**R**) whose period is 2a such that φ(x) = f(x) for |x| ≤ a, φ(x) = 0 for |x| > a }."
  - "For φ_1, φ_2 ∈ K(a), we set ⟨φ_1, φ_2⟩ = T_k(φ_1 ∗ φ̃_2)."
  - K(a) = K_odd(a) ⊕ K_even(a), "orthogonal with respect to ⟨ , ⟩" (p. 287).
- **The Fourier modes χ_n** (§3, "Positive definiteness for highly oscillating functions", p. 289).
  - χ_n(x) = (2a)^{−1/2} exp(πinx/a) for |x| ≤ a, and 0 for |x| > a.
  - "Then χ_n makes an orthonormal basis of L²([−a, a])."
- **The spaces K_N(a) and C_N(a)** (p. 290; also p. 282).
  - "K_N(a) = { φ ∈ K(a) | ∫_{−a}^{a} φ(x)exp(πinx/a) dx = 0 for all n ∈ **Z**, |n| ≤ N }, C_N(a) = C(a) ∩ K_N(a)."
- **Completions** (pp. 293–294).
  - Choose 2N+1-dimensional V ⊂ C(a) and W ⊂ K(a) with C(a) = V ⊕ C_N(a) and K(a) = W ⊕ K_N(a). Then Ĉ_N(a) and K̂_N(a) are the completions for ⟨ , ⟩, and Ĉ(a) = V ⊕ Ĉ_N(a), K̂(a) = W ⊕ K̂_N(a) (p. 293).
  - W(a) and V(a) are the ⟨ , ⟩-orthogonal complements of K̂_N(a) and Ĉ_N(a) (Prop. 3, p. 294).
  - "K̂(a) can be canonically embedded as a subspace of L²([−a, a]) and does not depend on the choice of W and N" (p. 282; Prop. 4 and the Remark, pp. 295–297).

### Results, in the paper's order
- **Introduction** (pp. 281–283).
  - "Then R.H. is equivalent to the positive definiteness of ⟨ , ⟩|C(a) for every a > 0 (cf. Proposition 2). It can easily be verified that ⟨ , ⟩|C(a) is positive definite if a is sufficiently small" (p. 281).
  - The problems posed (p. 282):
    - "(I) When a is given, can one determine whether ⟨ , ⟩|C(a) is positive definite or not?"
    - "(II) Study the deformation of ⟨ , ⟩|C(a) when a changes. What shall happen at the point a = a_0 beyond which ⟨ , ⟩|C(a) is not positive definite?"
  - Motivation: "the author's study of unitarizability problem of group representations [9]", and "the hope that the positive definiteness may become more tractable by cutting the support of functions, since the sum Σ_p for T(φ_1 ∗ φ̃_2), φ_1, φ_2 ∈ C(a) becomes a finite sum" (p. 282).
  - "We can prove the non-degeneracy of ⟨ , ⟩ on C(a) and on K(a) (Propositions 2 and 7), but to prove it on K̂(a) certainly requires more ideas" (p. 282).
  - "Concerning the problem (I), the existence of an algorithm to solve it is guaranteed by the estimate given by Lemma 9, §7. For an explicitly given a, the actual computation is not easy however. In §6 … when a = log 2/2: We find ⟨ , ⟩|K(a) is positive definite for a ≤ log 2/2 (Theorem 1). The idea is to calculate the hermitian matrix on W(a) with sufficient approximation for a suitably chosen N" (p. 283).
- **Proposition 1** (p. 285), introduced as "a slight sharpening of Weil's result".
  - "(1) T_k is oddly positive definite if and only if R.H. holds for ζ_k(s)."
  - "(2) T_k is evenly positive definite if and only if R.H. holds for ζ_k(s) with possible exceptions of real zeros, i.e. every non-trivial zero of ζ_k(s) lies on the critical line if it is not real."
- **Lemma 1** (p. 285). "Suppose that a non-trivial zero ρ_0 of ζ_k(s) and any positive number ε are given. Then there exists an α ∈ C_c^∞(**R**) such that M(α)(ρ_0) = 1, |M(α)(ρ)| ≤ ε/|ρ − ρ_0|² for every ρ ≠ ρ_0."
  - This is a test function normalised at one zero.
  - The proof of Prop. 1 uses it when RH fails at ρ_0 (p. 286). It builds an odd α for which Φ = M(α ∗ α̃) tends, as ε → 0, to −1 at each of ρ_0, ρ̄_0, 1 − ρ_0, 1 − ρ̄_0 (to −4 if ρ_0 is real), and is O(ε²) at the other zeros. Hence T_k(α ∗ α̃) < 0 for small ε.
- **Lemma 2** (p. 289). "There exists a_0 > 0 such that ⟨φ, φ⟩ > 0 for every φ ∈ K(a), φ ≠ 0 if a ≤ a_0."
  - The proof ends: "If a_0 is sufficiently small, we can find µ > 0 such that ⟨φ, φ⟩ > µ‖φ‖²_{L²} for every φ ∈ K(a), a ≤ a_0."
- **Lemma 3** (p. 290). "Suppose that a_0 > 0 and µ > 0 are given. Then there exists a non-negative integer N such that ⟨φ, φ⟩ ≥ µ‖φ‖²_{L²} for every φ ∈ K_N(a), 0 < a ≤ a_0."
- **Proposition 2 and Corollary** (p. 291).
  - Prop. 2: "For any a > 0, the restriction of the hermitian form ⟨ , ⟩ to C(a) is non-degenerate."
  - Proof idea: the radical has dimension ≤ 2N + 1 and is stable under d/dx, so its elements solve a linear ODE, which no nonzero element of C_c^∞ does.
  - Corollary: "The hermitian form ⟨ , ⟩ considered on C_c^∞(**R**) is non-degenerate."
- **Lemmas 4–6 and Propositions 3–4** (pp. 291–297).
  - Lemmas 4–5 are continuity (upper) bounds, e.g. Lemma 5: |⟨φ_1, φ_2⟩| ≤ c(‖φ_1‖_{L²} + ‖φ_1′‖_{L²})‖φ_2‖_{L²} for φ_1 ∈ C(a), φ_2 ∈ K(a).
  - Lemma 6: the form extends to K̂(a) and Ĉ(a).
  - Prop. 3: the orthogonal complements W(a), V(a) exist.
  - Prop. 4: "The canonical map K̂(a) → L²([−a, a]) is injective."
- **§5 Gram entries of the Fourier basis** (pp. 297–302).
  - "The positive definiteness of ⟨ , ⟩|K(a) is, roughly speaking, equivalent to the positive definiteness of the infinite dimensional hermitian matrix ((⟨χ_n, χ_m⟩)). Thus we are interested in calculating ⟨χ_n, χ_m⟩ explicitly" (p. 297).
  - (5.15) and (5.16) (p. 301) give closed forms with four ingredients:
    - the pole term (4/a)(e^{a/2} − e^{−a/2})²(1 − 4π²nm/a²)/({1 + (2πn/a)²}{1 + (2πm/a)²});
    - log A_k;
    - a finite prime sum over e log N(𝔭) ≤ 2a;
    - archimedean terms, as rapidly convergent series Σ_k … exp(−2a(2k + 1/2)) plus digamma values at 1/4 + πin/2a (and at 1/2 + πin/a when r_2 > 0).
  - "From (5.15) and (5.16), we can easily deduce the following. There exists κ > 0 which depends only on a such that (5.17) |⟨χ_n, χ_m⟩| ≤ κ/|n − m| if n ≠ m, (5.18) ⟨χ_n, χ_n⟩ ∼ (r_1 + 2r_2) log |n| for |n| → ∞" (pp. 301–302).
  - "If R.H. holds, the finite dimensional matrix ((⟨χ_n, χ_m⟩) | |n|, |m| ≤ N) must be positive definite for every N and a. We have verified this for several instances of a and N when k = **Q**" (p. 302).
- **Theorem 1** (p. 310). "Let a = log 2/2. We have ⟨φ, φ⟩ = T_**Q**(φ ∗ φ̃) ≥ 0 for every φ ∈ K(a), where equality holds if and only if φ = 0."
- **§7 (Continuity)** (pp. 311–319).
  - Proposition 5: "the matrix coefficients ⟨(α_i)_t − v_i(t), (α_j)_t − v_j(t)⟩ are continuous functions of t for 0 < t ≤ 2" (p. 311).
  - Lemma 7: T_k(α_t) is continuous in t for admissible α (p. 312).
  - Lemma 8: f_{ik}(t) is continuous (p. 313).
  - Lemma 9 is quoted under Q2.
- **§8 (Reduction to non-degeneracy)** (pp. 319–324).
  - Lemma 10 (p. 319): mollification is continuous for T_k.
  - **Proposition 6** (p. 320). "Assume that the Riemann hypothesis does not hold for ζ_k(s). Then there exists a_0 > 0 which has the following properties.
    - (1) If a ≤ a_0, ⟨ , ⟩|K(a) is positive semi-definite and ⟨ , ⟩|C(a) is positive definite.
    - (2) If a > a_0, both of ⟨ , ⟩|K(a) and ⟨ , ⟩|C(a) are not positive semi-definite."
  - **Theorem 2** (p. 321). "The Riemann hypothesis for ζ_k(s) holds if and only if the hermitian form ⟨ , ⟩ on K̂(a) is non-degenerate for every a > 0."
    - "RH false ⇒ degenerate": by Prop. 6 and the continuity in Prop. 5, "⟨ , ⟩|W(a) degenerates at a = a_0".
    - "RH ⇒ non-degenerate": if ⟨φ, φ⟩ = 0 then Φ = M(φ) vanishes at every zero. "This shows that Φ(s) is an entire function of order ≤ 1, exponential type a … n(r) = O(r) if Φ ≠ 0 … It is known that N(r) ≠ O(r) (cf. Siegel [6], Satz 2). This is a contradiction if Φ ≠ 0" (pp. 321–322).
  - **Proposition 7** (p. 322). "If k = **Q**, the hermitian form ⟨ , ⟩ on K(a) is non-degenerate for every a > 0."

### RH-equivalences actually in the paper
1. Weil's criterion, quoted (pp. 281, 285).
2. RH ⟺ ⟨ , ⟩|C(a) is positive definite for every a > 0 (p. 281, via Prop. 2).
3. Proposition 1 (p. 285):
   - RH ⟺ T_k is oddly positive definite;
   - evenly positive definite ⟺ RH apart from real zeros.
4. Theorem 2 (p. 321): RH ⟺ non-degeneracy on K̂(a) for every a > 0.
5. Proposition 6 (p. 320): if RH fails, there is a critical window a_0.
6. Remark on p. 302: RH ⇒ (⟨χ_n, χ_m⟩)_{|n|,|m|≤N} is positive definite for all N and a.
   - *Inference:* the converse also holds, by Weil's criterion. Approximate φ ∈ C(a) by its Fourier partial sums and use (5.17)–(5.18) together with Hilbert's inequality to control the form. Yoshida does not state the converse.

### Second-hand claims (from the earlier note) checked against the paper
| Claim (earlier note) | Status | What the paper says |
|---|---|---|
| Thm 1 = "W_∞(f) ≥ 0 for smooth positive-definite f with support in (1/2, 2) and f̂(±i/2) = 0" (Connes's restatement) | **Paraphrase, not Yoshida's statement** | Thm 1 (p. 310): T_ℚ(φ ∗ φ̃) ≥ 0 for every φ ∈ K((log 2)/2), with equality iff φ = 0 (details below the table). |
| Lemma 2: positive definite on K(a) for small a | Correct | Strict positivity (p. 289). The proof gives a margin µ‖φ‖²_{L²}, uniform in a ≤ a_0. |
| Lemma 3: ⟨φ,φ⟩ ≥ µ‖φ‖ on K_N(a) | Correct up to the norm | It is the **squared** norm, µ‖φ‖²_{L²}, uniform in 0 < a ≤ a_0 (p. 290). This resolves the earlier open point. |
| (5.17)–(5.18): off-diagonal ≪ 1/\|m−n\|, diagonal ∼ log\|n\|, for χ_n = e^{πinx/a} | Correct, with two precisions | χ_n = (2a)^{−1/2}e^{πinx/a}·1_{[−a,a]}; κ "depends only on a"; the diagonal is ∼ (r_1 + 2r_2) log\|n\| = [k:ℚ]·log\|n\| (pp. 289, 301–302). |
| RH ⟺ non-degeneracy on K̂(a) for every a | Correct | Theorem 2 (p. 321), for any Dedekind zeta function. |
| zbMATH: he "succeeded in proving the positive definiteness … on C(a) and K(a)" | **Inaccurate** | The paper proves *non-degeneracy*: on C(a) for all k and a (Prop. 2), and on K(a) only for k = ℚ (Prop. 7). Positive definiteness is proved only for small a (Lemma 2) and for a = (log 2)/2, k = ℚ (Thm 1). |
| Suzuki: non-degenerate on C(a) and K(a) for every a (Props 2, 7) | Correct but incomplete | Proposition 7 is only for k = ℚ. |
| Bombieri: positivity on a fixed interval reduces to a finite calculation; verified for t = (log 2)/2 | Correct | The intro (p. 283) credits Lemma 9 for the algorithm. §6 does the computation, "though it does not follow the algorithm faithfully". |

Details for the first row (Theorem 1 versus Connes's restatement):
- Yoshida has no f̂(±i/2) = 0 hypothesis, and the pole term is included. For odd φ that term is negative, −2|∫φ e^{x/2}|², by (6.2) on p. 302.
- Since supp(φ ∗ φ̃) ⊂ [−log 2, log 2] and (φ ∗ φ̃)(±log 2) = 0, no prime contributes. The statement therefore concerns only the archimedean and pole terms.
- Connes's version is the specialisation in which the pole terms vanish.

---

## Q2. Gram matrices of specific test functions; Gram–Schmidt, Cholesky, LDLᵀ, determinants, eigenvalues, lattices

**Gram matrices that do occur.**
- **Fourier modes χ_n of a window** — modulated indicators of [−a, a] (§5, pp. 297–302). This is the paper's central object (quotes under Q1).
- **Real modes** ω_n (§6). Sine modes on p. 305: ω_n = a^{−1/2} sin(πnx/a) = (√2/2i)(χ_n − χ_{−n}), with (6.10) ⟨ω_n, ω_m⟩ = ⟨χ_n, χ_m⟩ − ⟨χ_n, χ_{−m}⟩. Cosine modes on p. 309: ω_0 = χ_0, ω_n = 2^{−1/2}(χ_n + χ_{−n}).
- **Schur-complement Gram matrices** (⟨ω′_i, ω′_j⟩) (§6):
  - 10 × 10 for odd functions and 200 × 200 for even functions;
  - ω′_i = ω_i − v_i, where v_i is the Riesz representative of v ↦ ⟨v, ω_i⟩ on the high-mode space (pp. 306, 309).
- **Dilated bases** ((α_i)_t) of W and dilated modes χ_n(t) (§7). "By (7.2), we have ⟨(α_i)_t, (α_j)_t⟩ = T_k((α_i ∗ α̃_j)_t)" (p. 311), and "χ_n(t) = (χ_n(1))_t × √t" (p. 313).

**Each item on the requested list.**

| Item | Present? | Where and how |
|---|---|---|
| Dilations | Yes | α_t(x) = t^{−1}α(t^{−1}x) (§7, p. 311). Used to compare windows a and ta; there is no dilation orbit of test vectors. |
| Translates | Only incidentally | "(δ_u ∗ φ)(y) = φ(y − u) for every u ∈ **R**" (p. 322). This is the action of the prime-power masses of T_ℚ on φ in the proof of Prop. 7, not a family of test vectors. |
| Characteristic functions of intervals | One | χ_0 = ω_0 = (2a)^{−1/2}·1_{[−a,a]} (pp. 289, 309). Its Gram entries are the n = 0 cases of (5.15)–(5.16), and it is the first vector of the 200 × 200 even matrix. No family of interval indicators is used. |
| Point masses at log n | Only inside the distribution | (8.3) (p. 322): T_ℚ = e^{x/2} + e^{−x/2} − (log π)δ_0 − Σ_p Σ_{e≥1} (log p/p^{e/2})(δ_{e log p} + δ_{−e log p}) + V_1. Never used as test functions. |
| Dirichlet polynomials, 1_{(0,n]}, Mellin n^s/s | No | All test functions have compact support and entire Mellin transforms (p. 283). |
| Gram–Schmidt | Yes (§7) | "Let {ψ_k(t)} be the orthonormal basis of K̂_N(ta) obtained from {η_k(t)} by the Schmidt orthogonalization process" (p. 312). Here η_1 = χ_{N+1}(t), η_2 = χ_{−(N+1)}(t), …, η_{2n−1} = χ_{N+n}(t), η_{2n} = χ_{−(N+n)}(t). (7.6) is the usual recursion, whose denominators ‖η_k − Σ_{n<k}⟨η_k, ψ_n⟩ψ_n‖ are the square roots of the Gram–Schmidt pivots. |
| Cholesky | Yes, though not named | Proof of Lemma 9: C = (c_ij) and D = (d_ij) are "infinite dimensional lower triangular matrices", with (7.8) C ᵗC̄ = ((η_i, η_j)_1) (p. 315). The bounds are (7.19) ‖X_1^{−1}‖ ≤ κ_1^{−1} (p. 317) and (7.23) ‖X_4^{−1}‖ ≤ (µ(M) − κ_1^{−1}ν)^{−1} (p. 318), where X_1 and X_4 are diagonal blocks of C. |
| LDLᵀ / Gaussian elimination | Yes, as a numerical device (§6) | Odd case: "it suffices to show det(u_ij; 1 ≤ i,j ≤ k) > 0 for 1 ≤ k ≤ 10. The verification can be done by a simple triangulation process applied to U" (p. 307). Even case: see the quote below the table. |
| Determinants | Yes | Only the leading principal minors in the odd case (p. 307). |
| Smallest eigenvalues | No | The word does not occur. Prop. 6 and Thm 2 speak only of semi-definiteness and degeneracy of the matrix on W(a). |
| Lattices, integer vectors, shortest vectors | No | Integers appear only as Fourier indices and in the proof of Prop. 7 (see below). |

The even-case elimination (pp. 309–310): "The first step of the reduction of U to a diagonal form is done by adding −u_{i1}u_{1j}/u_{11} to u_{ij}, 2 ≤ i ≤ 200, 1 ≤ j ≤ 200. Repeated applications of this procedure succeed provided the diagonal entries are kept non-zero at every step. Using (6.23) and numerical values of ⟨ω_i, ω_j⟩, we can explicitly determine the lower and upper bounds which the matrix entries may take at every step. For our purpose, it suffices to observe that the lower bounds of every diagonal entries are positive at the final step. This fact can be verified rather easily on a computer."

The integers in the proof of Prop. 7 (pp. 323–324) are e_1 log p_1 − e_2 log p_2 = 2a (8.6), and then "p_1^{e_1}p_2^{−e_2} = p_3^{e_3}p_4^{−e_4}". This is a unique-factorisation argument showing that the jumps of φ at ±a, shifted by prime logarithms, cannot cancel.

**Lemma 9** (pp. 313–314), quoted in full.
- Set-up: "Let H be an infinite dimensional vector space over **C**. Let ( , )_1 and ( , )_2 be two positive definite hermitian forms on H … We assume that H is a separable Hilbert space with respect to ‖ ‖_1 and that H is embedded in the completion H* of H with respect to ‖ ‖_2. Let {ψ_n} be an orthonormal basis of H with respect to ‖ ‖_1 and let {η_n}, η_n ∈ H be an orthonormal basis of H*. We assume that {ψ_n} is obtained from {η_n} by the Schmidt orthogonalization process. Let T be a linear functional on H."
- Hypotheses:
  - (I) "There exists κ_1 > 0 such that ‖v‖_1 ≥ κ_1‖v‖_2 for every v ∈ H."
  - (I′) "There exists a sequence of positive numbers µ(M), M ∈ **N** such that lim_{M→∞} µ(M) = +∞ and that ‖v‖_1 ≥ µ(M)‖v‖_2 if v ∈ H satisfies (v, η_i)_2 = 0 for every i ≤ M."
  - (II) "There exists κ_2 > 0 such that |(η_j, η_l)_1| ≤ κ_2/|j − l| if j ≠ l."
  - (III) "There exists κ_3 > 0 such that |T(η_n)| ≤ κ_3 n^{−1}, n ≥ 1."
- Conclusion: "Then we have (Σ_{i>M} |T(ψ_i)|²)^{1/2} ≤ κ_3(1 + κ_1^{−2}ν)(µ(M) − κ_1^{−1}ν)^{−1}√(π²/6) for µ(M) > κ_1^{−1}ν, where ν = κ_2²(7π²/6 + 5π)."
- Application: H = K̂_N(ta), ( , )_1 = ⟨ , ⟩ and ( , )_2 = L² on [−ta, ta].
  - (I) holds by (7.3); (I′) follows from Lemma 3; (II) from (5.17); (III) from (3.1) and (5.17).
  - "the constants κ_1, κ_2, κ_3 and µ(M) can be taken independently of t when 1/2 ≤ t ≤ 2" (p. 314).
- Purpose: the uniform convergence of Σ_k |f_{ik}(t)|², which gives the continuity in Prop. 5 and hence Theorem 2. "This fact is by no means trivial but follows from the next Lemma" (p. 313).

---

## Q3. Every margin statement (lower bounds of the form ⟨φ,φ⟩ ≥ c‖φ‖², or comparisons)

None of these compares with a first term, a first vector or a fixed test vector. Every bound is relative to ‖φ‖²_{L²}, or is a bare positivity or robustness statement.

| # | Statement (page) | Space | Hypotheses | Bound | Uniformity |
|---|---|---|---|---|---|
| 1 | (2.4) (p. 288) | K(a), any a > 0 | Any k. C > 0 arbitrary; t_0 from (2.2); C_0, C′_0 from (2.3). Here C_1(a) = ∫_{−2a}^{2a}(e^{x/2}+e^{−x/2})dx and C_2(a) = #{(𝔭, m): m log N𝔭 ≤ 2a} (p. 287). | ⟨φ,φ⟩ ≥ {(r_1+2r_2)C + log A_k − C_1(a) − 2C_2(a)}‖φ‖²_{L²} − {r_1(C_0+C) + 2r_2(C′_0+C)}(1/2π)∫_{\|t\|≤t_0}\|φ̂\|²dt | Explicit in a. Useful only once the low frequencies are controlled, by (2.5) or by removing modes. |
| 2 | Proof of Lemma 2 (p. 289) | K(a), a ≤ a_0 | a_0 "sufficiently small"; any k; unconditional | ⟨φ,φ⟩ > µ‖φ‖²_{L²} | Uniform in a ≤ a_0; no modes removed. |
| 3 | Intro (p. 282); Lemma 3 (p. 290) | K_N(a), 0 < a ≤ a_0 | a_0 > 0 and µ > 0 given; N = N(a_0, µ, k); unconditional | ⟨φ,φ⟩ ≥ µ‖φ‖²_{L²} | Uniform in a ∈ (0, a_0]. Holds for every N′ ≥ N, since K_{N′}(a) ⊂ K_N(a). µ can be arbitrarily large. |
| 3′ | Instances of 3: (4.3) (p. 293); (7.3) (p. 311); proof of Thm 2 (p. 321) | (4.3): K_N(a). (7.3): K_N(b), 0 < b ≤ 2a. Thm 2: K_N(a), 0 < a ≤ a_1. | As in 3 | As in 3 | As in 3 |
| 4 | (6.3) (p. 302) | K(a), a = (log 2)/2, ‖φ‖_{L²} = 1, φ̌ = ±φ | k = ℚ | ⟨φ,φ⟩ ≥ −log π − (1/√2 − log 2) + (1/2π)∫\|φ̂\|² Re ψ(1/4 + it/2) dt | Single a. |
| 5 | (6.8) (p. 305) | K_10(a), a = (log 2)/2, φ odd or even | k = ℚ; t_1 = 50 in (6.7) | ⟨φ,φ⟩ ≥ 1.52‖φ‖²_{L²} | Single a; N = 10. |
| 6 | (6.9) (p. 305) | K_199(a) | k = ℚ; t_1 = 700 (see Q5) | ⟨φ,φ⟩ ≥ 4.08‖φ‖²_{L²} | Single a; N = 199. |
| 7 | (6.15)–(6.16) (pp. 306–307) | Odd 10 × 10 Schur complement | ‖v_i‖² ≤ ε = 1/40 | U = (u_ij), with u_ii = ⟨ω_i,ω_i⟩ − ε and u_ij = −\|⟨ω_i,ω_j⟩\| − ε, is positive definite | A robustness margin of one finite matrix. |
| 8 | (6.22)–(6.23) (pp. 309–310) | Even 200 × 200 Schur complement | ‖v_i‖² ≤ 1/2000 | Interval elimination: "the lower bounds of every diagonal entries are positive at the final step" | No values reported. |
| 9 | Theorem 1 (p. 310) | K(a), a = (log 2)/2 | k = ℚ | ≥ 0, with equality iff φ = 0 | No constant stated. |
| 10 | Lemma 9 (I), (I′) (p. 313); (7.19) (p. 317), (7.23) (p. 318) | Abstract H; applied to K̂_N(ta) | Coercivity assumed | ‖v‖_1 ≥ κ_1‖v‖_2; ‖v‖_1 ≥ µ(M)‖v‖_2 on (η_1,…,η_M)^⊥; ‖X_1^{−1}‖ ≤ κ_1^{−1}; ‖X_4^{−1}‖ ≤ (µ(M) − κ_1^{−1}ν)^{−1} | Constants independent of t ∈ [1/2, 2] (p. 314). |
| 11 | Prop. 6(1) (p. 320) | C(a), a ≤ a_0 | RH false | Positive definite, with no constant | — |

Not margins: Lemma 4 (pp. 291–292), Lemma 5 (pp. 292–293), (4.4)–(4.5) (p. 293) and (5.17) (p. 301) are upper (continuity) bounds.

*Inference.* Rows 2, 3, 5, 6 and 10 are all "coercivity on a subspace" statements. Their source is Re ψ(σ + it) ∼ log|t| (p. 288), i.e. the archimedean term dominates at high frequency. None of them concerns the low-mode block W(a), where Yoshida locates the arithmetic content (Thm 2 and p. 283).

---

## Q4. Anything resembling (A), (B), "each new vector keeps a fixed distance from the span of the previous ones", or extremal problems normalised at one coefficient

- **Comparison with a first vector or first term.** None anywhere in the paper.
- **"Each new vector keeps a distance from the span of the previous ones."**
  - The only instance is implicit, in Lemma 9.
  - In its notation, c_kk = ‖η_k − P_{k−1}η_k‖_1, where P_{k−1} is the ( , )_1-orthogonal projection onto span(η_1, …, η_{k−1}); c_kk² is the Gram–Schmidt pivot.
  - Since C is lower triangular, (X_1^{−1})_{ii} = 1/c_ii, so (7.19) gives c_ii ≥ κ_1 for all i. This also follows in one line from (I), because the η_i are ‖·‖_2-orthonormal.
  - Likewise (7.23) gives c_ii ≥ µ(M) − κ_1^{−1}ν for i > M.
  - So every pivot of the high modes is ≥ κ_1², and the pivots tend to infinity. Yoshida never states this; he uses only the operator-norm bounds.
  - **How it differs from (A)** (inference):
    - it is a consequence of coercivity on a high-frequency subspace;
    - it is unconditional;
    - it concerns one window's Fourier modes;
    - it never compares with d_1.

    In the repository's setting there is no coercivity, since λ_min(G_N) → 0 (≈ 0.048 log N/N per the earlier report). The pivot bound in (A) is therefore not of this operator-norm type.
  - The growth of these pivots (∼ log of the frequency, by (5.18)) parallels d_k ≫ log k in (A). *Heuristic inference:* both come from Re ψ(1/4 + it/2) ∼ log|t|. The part of w_k not in span(w_1, …, w_{k−1}) carries a jump of height √k at log k, on a scale ∼ 1/k, which gives energy ∼ k·(1/k)·log k.
- **Extremal problems normalised at one coefficient.** None is posed as such.
  - *Inference:* §6 computes such quantities without naming them.
    - ⟨ω′_i, ω′_i⟩ = min_{v ∈ K̂_N(a)} ⟨ω_i − v, ω_i − v⟩: the least Weil energy among functions whose i-th low-mode coefficient is 1 and whose other low-mode coefficients vanish.
    - The k-th elimination pivot of U is the minimum of ⟨φ, φ⟩ over φ = ω_k + Σ_{j<k} c_j ω_j + (high modes).
    - So the §6 pivots are the exact analogue of the repository's d_k, for the trigonometric basis of one window in frequency order. Yoshida only shows that interval lower bounds for them are positive.
  - Lemma 1 (p. 285) normalises on the zero side instead: M(α)(ρ_0) = 1, with |M(α)(ρ)| ≤ ε/|ρ − ρ_0|² elsewhere. It is used for the "⇐" half of Prop. 1.
- **(B), shortest vectors and integrality.** Nothing.
- **Mechanism shared with the repository** (inference).
  - The "RH ⇒ non-degenerate" half of Theorem 2 (pp. 321–322) runs: if ⟨φ, φ⟩ = 0, then M(φ) is entire of exponential type a and vanishes at every ρ, contradicting N(r) ≠ O(r).
  - The same argument shows that G_N is positive *definite* under RH. A nonzero P(s) = Σ_{n≤N} x_n n^s has exponential type log N, so it cannot vanish at all ρ.
  - Yoshida does not consider Dirichlet polynomials.

---

## Q5. Numerical computations

- **§5 remark (p. 302).** The finite matrices (⟨χ_n, χ_m⟩)_{|n|,|m|≤N} were "verified" positive definite "for several instances of a and N when k = **Q**". No values of a or N, no eigenvalues and no pivots are reported.
- **§6 set-up**: k = ℚ and a = (log 2)/2. The goal is (6.1): ⟨φ, φ⟩ ≥ 0 on K(a).
  - The prime terms vanish: the only candidate is p = 2, e = 1, with weight 2a − log 2 = 0. The computation is therefore purely archimedean plus pole.
  - Pole term (6.2): ∫(φ ∗ φ̃)(e^{x/2} + e^{−x/2})dx = 2ε|∫φ e^{x/2}dx|², with ε = ±1 for even/odd φ. For odd φ it is bounded via Schwarz by e^a − e^{−a} − 2a = 1/√2 − log 2. This gives (6.3).
  - Archimedean side: t_0 = 2.0320… is the zero of Re ψ(1/4 + it/2) (p. 303), and ∫_0^{t_0} Re ψ(1/4 + it/2) dt = −2.7626… (p. 305).
- **(6.7) and the explicit margins.**
  - (6.7) with t_1 = 50, N = 10: C = 3.2188…, giving (6.8) ⟨φ, φ⟩ ≥ 1.52‖φ‖²_{L²} on K_10(a).
  - With t_1 = 700, N = 199: "C = 5.9914…", giving (6.9) ⟨φ, φ⟩ ≥ 4.08‖φ‖²_{L²} on K_199(a).
- **Odd part** (pp. 305–309).
  - Modes ω_1, …, ω_10 (sines); the 10 × 10 matrix (⟨ω′_i, ω′_j⟩).
  - The comparison matrix U (u_ii = ⟨ω_i, ω_i⟩ − ε, u_ij = −|⟨ω_i, ω_j⟩| − ε) is positive definite with ε = 1/40. This is checked by leading minors and "a simple triangulation".
  - Tail: (6.18) |⟨ω_n, ω_m⟩| ≤ C_1 m^{−1} for n < m, with C_1² = 0.3508…, so Σ_k |⟨ω_i, ω_{k+10}⟩|² ≤ C_1²/10 = 0.03508… ≤ 1.52/40 = 0.038 (6.16).
- **Even part** (pp. 309–310).
  - Modes ω_0 = χ_0 (the indicator) and ω_1, …, ω_199 (cosines); the 200 × 200 matrix.
  - Perturbation tolerance 1/2000, by (6.22)–(6.23). Interval Gaussian elimination leaves positive lower bounds on all final diagonal entries.
  - Tail: (6.26)–(6.27) with C_2² = 0.3321…, so Σ_{k≥200} |⟨ω_i, ω_k⟩|² ≤ C_2²/199 = 0.001668… ≤ 4.08/2000 = 0.00204 (6.24).
  - Yoshida: "the actual computation becomes more cumbersome" (p. 309).
  - *Inference:* the much smaller tolerance and the larger matrix suggest the even block at this window is much closer to degenerate than the odd block. Yoshida reports no pivot or eigenvalue values.
- **What the computations show.** Theorem 1 only: strict positivity of the Weil form on K((log 2)/2) for k = ℚ. There is no margin constant and nothing for larger windows.
- **Recomputed here** (mpmath, from the formulas as printed):

  | Quantity | Recomputed | Printed |
  |---|---|---|
  | t_0 | 2.03206 | 2.0320… |
  | ∫_0^{t_0} Re ψ(1/4 + it/2) dt | −2.76263 | −2.7626… |
  | C for t_1 = 50 | 3.21886 | 3.2188… |
  | (6.7) bound for t_1 = 50, N = 10 | 1.539 | ≥ 1.52 |
  | C_1² | 0.35081 | 0.3508… |
  | C_2² | 0.332103 | 0.3321… |
  | C for t_1 = 700, i.e. Re ψ(1/4 + 350i) | 5.8579 | 5.9914… |

  - The printed C = 5.9914… is Re ψ(1/4 + 400i), i.e. t_1 = 800. So either t_1 or C is misprinted on p. 305.
  - Either way, (6.7) gives a margin of about 4.11 at N = 199 (4.115 for t_1 = 700, 4.113 for t_1 = 800). So (6.9)'s 4.08 stands.
  - Second misprint: p. 309 writes "v_i ∈ K̂_{10,even}(a)" where K̂_{199,even}(a) is meant, since η_n = ω_{n+199} and (6.9) is the bound used.
  - (5.15) at n = 0 is checked under "Dictionary" above.

---

## Q6. Scope (L-functions, function fields) and where positivity with a margin fails

- **Scope.**
  - The whole paper is set up for Dedekind zeta functions ζ_k of number fields k, with r_1, r_2, D_k and A_k (§1, (1.6), p. 284). This covers Prop. 1, Lemmas 2–3, Prop. 2, §4, §5, §7, Prop. 6 and Thm 2.
  - Only Theorem 1 (§6) and Proposition 7 are restricted to k = ℚ.
  - There are no Dirichlet, Hecke or Artin L-functions and no function fields. "Hecke" appears only in the title of Siegel's reference [6], cited for N(r) ≠ O(r).
  - The motivation is unitarizability of representations of p-adic groups (ref. [9], p. 282).
- **Where margins hold and fail, in the paper.**
  - Margins hold on small windows (Lemma 2) and on high Fourier modes (Lemma 3, (6.8)–(6.9)).
  - Lemma 2 needs a_0 small enough that (r_1+2r_2)C + log A_k − C_1(a_0) − 2C_2(a_0) − (2a_0/π)r_1(C_0+C)t_0 − (4a_0/π)r_2(C′_0+C)t_0 > 0 (p. 289). The pole growth C_1(a) and the prime count C_2(a) eventually defeat it.
  - Low frequencies threaten positivity on the archimedean side: Re ψ(1/4 + it/2) < 0 for |t| < t_0 = 2.03… (p. 303). For odd φ the pole term is negative (6.2).
  - If RH fails, Prop. 6 and the proof of Thm 2 show that the matrix of ⟨ , ⟩ on the finite block W(a) depends continuously on a. It is semi-definite up to the critical window a_0, degenerates there and is indefinite beyond it. Any margin on W(a) must therefore tend to 0 as a ↑ a_0.
  - Under RH the paper says nothing about a margin on W(a), or about any margin uniform in a.

---

## Gaps
- **Transcription.** The paper is a scan, and I transcribed the formulas by eye. I re-derived or numerically checked the constants and formulas used above: (5.15) at n = 0, t_0, the Re ψ integral, (6.7)–(6.9), C_1² and C_2². I did not check (5.16) or (6.17)/(6.25) numerically.
- **Not reproduced.** The 10 × 10 and 200 × 200 matrices, so their actual pivot or eigenvalue sizes at a = (log 2)/2 remain unknown. Yoshida does not report them.
- **Not checked.** Yoshida's preprint [9], on unitarizability of principal series of p-adic Chevalley groups, and any later work by Yoshida on these forms.
- **Scripts.** The numerical checks were run from `/tmp/claude-0/-home-user-number-theory/05c185b2-2246-5d9e-ba9c-98c8d169fd20/scratchpad/scripts/` (`check_515.py`, `check_515b.py`, `check_67.py`). This is session scratch space and may not persist.
