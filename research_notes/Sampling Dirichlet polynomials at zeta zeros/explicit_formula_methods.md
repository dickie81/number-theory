# Explicit-formula methods with band-limited test functions (and |A|²·w test functions) for zeros of ζ(s)

Scope: where the Guinand–Weil explicit formula is used with test functions whose Fourier transform has compact support, and especially with test functions of the form |A(t)|²·w(t) (A a Dirichlet polynomial). The goal is to identify the predecessors of the method under review: the explicit formula applied to h = |D|²Φ, where Φ is a band-limited minorant of ¼·1_[−T,T] that vanishes to second order at 0 and has supp Φ̂ ⊂ [−36/T, 36/T]. For T > 72N, both the diagonal and the Landau prime-side form are then exact. The notes also try to say what is new.

Notation used below: "Guinand–Weil (GW)" is the form quoted by Goldston–Gonek and by Carneiro–Milinovich–Soundararajan. For h analytic in |Im s| ≤ ½+ε with |h(s)| ≪ (1+|s|)^{−1−δ}, the identity reads

Σ_ρ h((ρ−½)/i) = h(1/2i) + h(−1/2i) − (1/2π) ĥ(0) log π + (1/2π)∫ h(u) Re Γ′/Γ(¼ + iu/2) du − (1/2π) Σ_{n≥2} Λ(n) n^{−1/2} (ĥ(log n/2π) + ĥ(−log n/2π)),

with ĥ(x) = ∫ h(w) e^{−2πixw} dw.

---

## 1. Montgomery's pair-correlation line (Montgomery 1973; Goldston–Montgomery 1987; Gallagher 1985; Goldston–Gonek–Özlük–Snyder 2000). Do any of these evaluate Σ_γ |Σ_n a_n n^{iγ}|² w(γ) for general coefficients via a band-limited explicit formula, and in what range?

### Takeaway
None of these four works evaluates a one-level sum Σ_γ |Σ_n a_n n^{iγ}|² w(γ) with general coefficients. All of them study the two-level (pair-correlation) statistic F(α) = Σ_{γ,γ′} T^{iα(γ−γ′)} w(γ−γ′). Montgomery obtains it by squaring his explicit formula for Σ_γ x^{iγ}/(1+(t−γ)²) and integrating over t ∈ [0,T], using a continuous mean-value theorem for a Dirichlet series with the fixed coefficients Λ(n)a_n(x). Band-limitation enters on the pair-correlation side: sums over differences of zeros are evaluated exactly in the limit for r with r̂ supported in [−1,1], and Gallagher and Carneiro–Chandee–Littmann–Milinovich use Beurling–Selberg-type majorants and minorants in that class. What carries over to the note is the principle and the kernels (Fejér, Selberg minorant), not the sum it evaluates.

### Cited Findings
- **Montgomery's explicit formula.** In Goldston's exposition, Proposition 1 (eq. 3.11) is "due to Montgomery [27]". It is proved from Landau's 1909 explicit formula. Under RH and for x ≥ 1 it expresses 2x^{1/2−it} Σ_γ x^{iγ}/(1+(t−γ)²) as −Σ_n Λ(n) a_n(x) n^{−it}, plus a pole/main term, plus x^{−1/2}(log(|t|+2)+O(1)), plus an error term, where a_n(x) = min((n/x)^{1/2}, (x/n)^{3/2}). (Transcribed from a PDF text extraction; the lower-order terms are not reproduced exactly here.) Goldston remarks that "The role of RH in Proposition 1 is notational." — [Goldston, Notes on pair correlation of zeros and prime numbers, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Squaring and integrating.** "Montgomery was interested in studying the distribution of the differences of pairs of zeros, and for this it is clear one needs to square the absolute value of the sum over zeros… we also integrate with respect to t." This gives F(x,T) = Σ_{0<γ,γ′≤T} x^{i(γ−γ′)} w(γ−γ′) = (2/π)∫_{−∞}^{∞} |Σ_{0<γ≤T} x^{iγ}/(1+(t−γ)²)|² dt with w(u) = 4/(4+u²). The prime side is handled by "a standard mean value theorem of Montgomery and Vaughan", ∫_0^T |Σ a_n n^{−it}|² dt = Σ |a_n|² (T + O(n)). — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Montgomery's theorem (as stated by Goldston).** "Assume the Riemann Hypothesis. Then F(α) is real, even, and non-negative. Further, uniformly for 0 ≤ α ≤ 1 − ε, we have F(α) = α + o(1) + (1 + o(1))T^{−2α} log T." Using a sieve bound for prime twins (Goldston–Montgomery), the range extends to 0 ≤ α ≤ 1. — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **The band-limited principle.** Goldston writes Σ_{γ,γ′} r(γ−γ′ · log T/2π) w(γ−γ′) = (T/2π) log T ∫ r̂(α)F(α) dα, and then: "we can evaluate sums over differences of zeros on the class of functions whose Fourier transforms are supported in [−1, 1]." He uses the Fejér pair k(u) = (sin πλu/πλu)², k̂(α) = (1/λ)max(1 − |α|/λ, 0). With λ = 1 this gives Σ m_ρ ≤ (4/3+ε)(T/2π) log T, hence at least 2/3 of the zeros are simple (on RH). — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Gallagher (1985).** CCLM write that Montgomery's formula, for admissible R (R̂ supported in [−1,1]), gives (1/N(T)) Σ R((γ′−γ) log(T/2π)/2π) w(γ′−γ) → R(0) + ∫ R(x)(1 − (sin πx/πx)²) dx. "In [19], Gallagher considered the case β ∈ ½ℕ, for which a classical construction of Beurling and Selberg… produces admissible majorants and minorants r_β^± … When β ∈ ½ℕ, the Fourier transforms r̂_β^± have simple explicit representations as finite series." Gallagher also "solved the two-delta problem." The reference is P. X. Gallagher, Pair correlation of zeros of the zeta function, J. reine angew. Math. 362 (1985), 72–86. — [Carneiro–Chandee–Littmann–Milinovich, arXiv:1406.5462](https://arxiv.org/abs/1406.5462)
- **Gallagher–Mueller.** Gallagher and Mueller (Crelle 303/304 (1978)) assumed an asymptotic pair-correlation density and replaced Montgomery's theorem by Fujii/Selberg results on S(T). This is again two-level, not a Dirichlet-polynomial sum over zeros. — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Goldston–Montgomery (1987)**, "Pair correlation of zeros and primes in short intervals", in Analytic Number Theory and Diophantine Problems, Birkhäuser 1987, 183–203. Goldston summarises it as showing that "one can prove on RH that SPC is equivalent to ∫_1^X (ψ(x+h) − ψ(x) − h)² dx ∼ hX log(X/h) for 1 ≤ h ≤ X^{1−ε}". This is a statement about prime variances, not about Dirichlet polynomials sampled at zeros. — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Goldston–Gonek–Özlük–Snyder (Proc. LMS 80 (2000), no. 1, 31–49, DOI 10.1112/S0024611500012211).** They use "an approximation for the prime indicator function, a new mean value theorem for long Dirichlet polynomials, and bounds on tails of Dirichlet series". Assuming GRH for all Dirichlet L-functions, they prove F(α) ≥ 3/2 − |α| − ε for 1 ≤ |α| ≤ 3/2 − 2ε (abstract as summarised from the Cambridge page). — [Cambridge Core abstract](https://www.cambridge.org/core/journals/proceedings-of-the-london-mathematical-society/article/abs/on-the-pair-correlation-of-zeros-of-the-riemann-zetafunction/29A91CBF07210A94E8EEFEAFFBB9FDEE)
- **The long mean-value tool.** Goldston–Gonek, "Mean value theorems for long Dirichlet polynomials and tails of Dirichlet series", Acta Arith. 84 (1998) 155–192, is a continuous-t mean-value tool. — [Goldston, arXiv:math/0412313 (reference list)](https://arxiv.org/abs/math/0412313)
- **Ranges.** Montgomery's method works for x = T^α with α ≤ 1 (Dirichlet-series length up to T, by the Montgomery–Vaughan mean-value theorem). For x ≥ T, F(x,T) = (1/2πx)∫_0^T |Σ_n Λ(n)a_n(x) n^{−it} − (main term)|² dt + o(T log T), and the off-diagonal terms "must almost perfectly cancel". — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)

### Inferences
- The note's Σ_γ |D(γ)|²Φ(γ) = Σ_{m,n} b_m b_n Σ_γ (m/n)^{iγ}Φ(γ) is a one-level statistic: a linear combination of exponential sums over zeros, which Landau's formula controls. Montgomery's F(α) is two-level. So the pair-correlation papers are predecessors only for (i) the principle that restricting the Fourier support makes the arithmetic side computable, and (ii) the kernels (Fejér; Selberg's minorant (sin πu/πu)²/(1−u²)).
- Montgomery's prime side uses the specific coefficients Λ(n)a_n(x). The note uses general real b_n and needs only Mertens plus a Schur test. The Landau form 2Σ_k Λ(k)k^{−1/2}Σ_{jk≤N} b_j b_{jk} does not appear in these four papers.

### Gaps
- Montgomery 1973 (Proc. Sympos. Pure Math. 24, 181–193), Goldston–Montgomery 1987, Gallagher 1985 and the full text of GGOS 2000 were not consulted directly. Their content is taken from Goldston's notes, the CCLM paper and the Cambridge abstract.
- I could not verify whether Montgomery's ICM 1974 address or Gallagher 1985 states a general Dirichlet-polynomial mean value over zeros. No source found says so.

---

## 2. Fourier optimisation with the explicit formula and Beurling–Selberg-type extremal functions. Which papers use exact minorants or majorants of indicators (or of other functions) with the explicit formula to count zeros or bound sums over zeros?

### Takeaway
The modern template comes from Goldston–Gonek (2007): GW plus Beurling–Selberg majorants and minorants F± of 1_[−L,L] with F̂± = 0 for |x| ≥ δ, applied to h(w) = F(w − t). Goldston–Gonek say their Lemma 2 "is essentially Lemma 2" of Montgomery–Odlyzko (1984), so that paper is the earlier source of the combination GW plus band-limited majorant/minorant. The Carneiro–Chandee–Milinovich school, Chandee–Soundararajan and Carneiro–Milinovich–Soundararajan developed it into optimal (Gaussian-subordination or de Branges-space) extremal problems.

In all of these the test function is a single band-limited function, translated or modulated. Supports grow like log log t, so the prime side is a short sum bounded trivially. None of them uses |A|²·w with a long Dirichlet polynomial A, and none tunes the support against the 1/N spacing of {log(m/n)}.

### Cited Findings
- **Goldston–Gonek 2007, Lemma 1.** This is GW in the form above. "This is a specialization of Theorem 5.12… of [Iwaniec–Kowalski]. The conditions in [1] are that ĥ is an infinitely differentiable function with compact support." — [Goldston–Gonek, arXiv:math/0511092 (Bull. LMS 39 (2007) 482–486)](https://arxiv.org/abs/math/0511092)
- **Goldston–Gonek 2007, Lemma 2.** It provides even entire F± with: F− ≤ χ_[−L,L] ≤ F+; ∫F+ ≤ 2L + 1/δ and ∫F− ≥ 2L − 1/δ; F±(w) ≪ e^{2πδ|Im w|}; F±(u) ≪ min(1, δ^{−2}(|u|−L)^{−2}) for |u| > L; F̂±(x) = 0 for |x| ≥ δ; F̂±(x) = sin(2πLx)/(πx) + O(1/δ). "This is essentially Lemma 2 from [4] [Montgomery–Odlyzko]. Functions of this type were constructed by A. Selberg… For a proof of this lemma, see H. L. Montgomery [3] and J. D. Vaaler [6]." Here [3] is Montgomery, "The analytic principle of the large sieve", Bull. AMS 84 (1978) 547–567, and [6] is Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985) 183–216. — [Goldston–Gonek, arXiv:math/0511092](https://arxiv.org/abs/math/0511092)
- **Goldston–Gonek 2007, the proof.** They take h(w) = F(w − t). The pole terms are ≪ e^{πδ} by exponential type. The prime sum runs only over n < e^{2πδ} and "was estimated trivially" (≪ e^{πδ}), with πδ = log log t − 2 log log log t.
  - Theorem 1 (RH, 0 < h ≤ √t): N(t+h) − N(t) − (h/2π)log(t/2π) ≤ (½+o(1)) log t/log log t.
  - Theorem 2: |S(t)| ≤ (½+o(1)) log t/log log t.
  - Corollary 1: m(γ) ≤ (½+o(1)) log γ/log log γ, and γ′ − γ ≤ π(1+o(1))/log log γ.
  — [Goldston–Gonek, arXiv:math/0511092](https://arxiv.org/abs/math/0511092)
- **Carneiro–Chandee–Milinovich, Math. Ann. 356 (2013) 939–968.** "Assuming the Riemann hypothesis, we present two proofs of the bound |S(t)| ≤ (¼ + o(1)) log t/log log t… This improves a result of Goldston and Gonek by a factor of 2." One proof bounds S_1(t) with Carneiro–Littmann–Vaaler extremal functions. The other solves "the Beurling–Selberg extremal problem for the odd function f(x) = arctan(1/x) − x/(1+x²)". — [arXiv:1309.1526](https://arxiv.org/abs/1309.1526)
- **Carneiro–Chandee–Milinovich, Math. Z. 281 (2015) 315–332.** "We give a new and simple proof of the sharpest known bound for S(t)… We also prove a number of related results including bounding the order of vanishing of an L-function at the central point and bounding the height of the lowest zero of an L-function." In the text: "As in the work of Goldston and Gonek… we use the explicit formula in conjunction with the classical majorants and minorants of exponential type for characteristic functions of intervals that were constructed by Beurling and Selberg." There is a GL(m) version: |S(t,π)| ≤ (m/4) log t/log log t + O(…). — [arXiv:1503.00955](https://arxiv.org/abs/1503.00955)
- **Chandee–Soundararajan (Bull. LMS 2011).** "The problem of bounding |ζ(1/2+it)| may be framed in terms of minorizing the function log((4+x²)/x²) by functions whose Fourier transforms are supported in a given interval, and drawing upon recent work of Carneiro and Vaaler we find the optimal such minorant. Thus we establish that any C > (log 2)/2 is permissible in Littlewood's result." They describe the Goldston–Gonek method as "the explicit formula together with certain optimal majorants and minorants of characteristic functions of intervals that were constructed by Selberg." — [arXiv:0908.2008](https://arxiv.org/abs/0908.2008)
- **Carneiro–Chandee, "Bounding ζ(s) in the critical strip".** This extends Chandee–Soundararajan to log|ζ(α+it)| using extremal majorants and minorants of prescribed exponential type for log((4+x²)/((α−½)²+x²)). — [arXiv:1008.4970](https://arxiv.org/abs/1008.4970)
- **Carneiro–Chirre–Milinovich, Publ. Mat. 63 (2019) 601–661.** They give explicit RH bounds for the argument and its antiderivatives in the critical strip. "An important element in our strategy is the ability to solve a Fourier optimization problem with constraints, namely, the problem of majorizing certain real-valued even functions by bandlimited functions, optimizing the L¹(ℝ)-error." — [arXiv:1710.10362](https://arxiv.org/abs/1710.10362)
- **Carneiro–Chandee–Littmann–Milinovich, J. reine angew. Math. 725 (2017) 143–182.** "Assuming the Riemann hypothesis, we prove upper and lower bounds for N(T,β)… using Montgomery's formula and some extremal functions of exponential type… optimal in the sense that they majorize and minorize the characteristic function of the interval [−β, β] in a way to minimize the L¹(ℝ, {1 − (sin πx/πx)²}dx)-error… using the framework of reproducing kernel Hilbert spaces." This "extends previous work by P. X. Gallagher in 1985". — [arXiv:1406.5462](https://arxiv.org/abs/1406.5462)
- **Carneiro–Milinovich–Soundararajan, Comment. Math. Helv. 94 (2019) 533–568.**
  - Lemma 6 is GW (from Iwaniec–Kowalski Thm 5.12). They "fix F… even and bandlimited Schwartz function, with F(0) > 0… supp(F̂) ⊂ [−N, N]". They apply GW "to the entire function h(z) = f(z)a^{iz}" with f(z) = ΔF(Δz). This is a band-limited function times a single Dirichlet monomial.
  - Theorem 5 (RH): "for x ≥ 4, there is always a prime number in the interval [x, x + (22/25)√x log x]."
  — [arXiv:1708.04122](https://arxiv.org/abs/1708.04122)
- **Chirre–Pereira–de Laat.** "Assuming the generalized Riemann hypothesis, we give asymptotic bounds on the size of intervals that contain primes from a given arithmetic progression using the approach developed by Carneiro, Milinovich and Soundararajan… we extend the Guinand-Weil explicit formula over all Dirichlet characters modulo q ≥ 3, and… reduce the associated extremal problems to convex optimization problems… via semidefinite programming." — [arXiv:2005.02393](https://arxiv.org/abs/2005.02393)
- **Chirre–Gonçalves–de Laat.** They use "semidefinite programming to improve upon numerous asymptotic bounds" via Montgomery's pair-correlation approach (proportion of distinct zeros, small gaps, sums of multiplicities). — [arXiv:1810.08843](https://arxiv.org/abs/1810.08843)
- **Carneiro–Chandee–Chirre–Milinovich.** "On Montgomery's pair correlation conjecture: a tale of three integrals" gives new upper and lower bounds via "new connections to certain extremal problems in Fourier analysis". — [arXiv:2108.09258](https://arxiv.org/abs/2108.09258)
- **Carneiro–Chirre–Milinovich, "Hilbert spaces and low-lying zeros of L-functions".** It generalizes Iwaniec–Luo–Sarnak (2000) non-vanishing proportions via one-level density with RKHS optimisation. It also revisits "the height of the first low-lying zero in a family, considered by Hughes and Rudnick (2003) and Bernard (2015)". — [arXiv:2109.10844](https://arxiv.org/abs/2109.10844)

### Inferences
- **The explicit-formula skeleton is already standard.** The note's GW statement (h analytic in a strip, decay, ĥ compactly supported; pole term h(±i/2); Γ′/Γ archimedean term; prime sum over Λ(n)n^{−1/2}ĥ(±log n/2π)) is the Goldston–Gonek / CMS Lemma. It should be cited to Iwaniec–Kowalski Thm 5.12, as those papers do.
- **How the note differs from this school.**
  - (a) The test function is not a translate F(w − t) or a modulated band-limited function f(z)a^{iz}. It is |D|²Φ, a superposition of N² modulated band-limited functions (m/n)^{iz}Φ(z). CMS's h(z) = f(z)a^{iz} is the one-term case.
  - (b) The support is not tuned to log log t. It is tuned to the arithmetic separation of {log(m/n)}, i.e. 36/T < 1/(2N).
  - (c) As a result the prime side is not bounded trivially. It equals the Landau form exactly.
  - (d) Pole-term control comes from vanishing at 0 together with exponential type, not from exponential type alone (≪ e^{πδ}).

### Gaps
- Montgomery–Odlyzko 1984 (Colloq. Math. Soc. János Bolyai 34, 1079–1106) was not accessible. That its Lemma 2 is the Beurling–Selberg lemma rests on Goldston–Gonek's statement.
- I found no paper by Chirre or coauthors on discrete mean values of Dirichlet polynomials at zeros.

---

## 3. Weighted zero sums with a Dirichlet polynomial squared: which works use h(t) = |A(t)|²·(weight) with an explicit formula, or otherwise evaluate Σ_γ |A(γ)|² w(γ)?

### Takeaway
The closest predecessor is the Montgomery–Odlyzko method (1984) for gaps between zeros. Under RH it uses GW with a Dirichlet polynomial A of length K = T(log T)^{−2} (Bui–Milinovich–Ng) or y = T^{1−δ} (Goldston–Trudgian–Turnage-Butterbaugh). It produces exactly a weighted Landau form, Re Σ_{nk≤K} a_k ā_{nk} g_c(n)Λ(n)n^{−1/2}, as the off-diagonal term, with o(1) errors. Conrey–Ghosh–Gonek (1984) recast it as M2(c)/M1, the ratio of Σ_γ ∫_{|α|≤πc/log T} |A(γ+α)|² dα to ∫_T^{2T} |A|². Inoue–Kobayashi–Toma (2025/26) run a resonance version: an explicit formula for log ζ applied termwise to (n/m)^{iz}·Gaussian.

Other discrete mean values with Dirichlet polynomials at zeros (Ng, Milinovich–Ng, Pearce-Crump 2026, Sinha 2025) use Gonek's uniform Landau formula or contour integration, not band-limited GW. Soundararajan's 2009 moment method uses an explicit-formula inequality for log|ζ| with a band-limited (triangle) weight, not |A|²w.

### Cited Findings
- **Montgomery–Odlyzko, as described by Bui–Milinovich–Ng.**
  - Setup: "Let T be large and put K = T(log T)^{−2}… h(c) := c − Re Σ_{nk≤K} a_k ā_{nk} g_c(n)Λ(n)n^{−1/2} / Σ_{k≤K}|a_k|², where g_c(n) = 2 sin(πc log n/log T)/(π log n)."
  - Result: "In [7], by an argument using the Guinand-Weil explicit formula for the zeros of ζ(s), Montgomery & Odlyzko show that if h(c) < 1 for some choice of c > 0 and a sequence {a_n} then λ ≥ c and that if h(c) > 1… then µ ≤ c."
  - Coefficients and outputs: a_k = f(log k/log K)/√k and λ(k)f(log k/log K)/√k, giving µ < 0.5179 and λ > 1.97.
  — [Bui–Milinovich–Ng, arXiv:0910.2052 (Proc. AMS 138 (2010) 4167–4175)](https://arxiv.org/abs/0910.2052)
- **Conrey–Ghosh–Gonek reformulation (Bull. LMS 16 (1984) 421–424).** "Let A(t) = Σ_{k≤K} a_k k^{−it}… M1 = ∫_T^{2T}|A(t)|²dt and M2(c) = ∫_{−πc/log T}^{πc/log T} Σ_{T≤γ≤2T}|A(γ+α)|² dα. Then… M2(µ) ≤ M1 ≤ M2(λ)… it can be shown that M2(c)/M1 = h(c) + o(1). Hence, this argument is seen to be equivalent to Montgomery & Odlyzko's method." Footnote: "Mueller [9] was the first to observe that this method gave a lower bound for λ." — [Bui–Milinovich–Ng, arXiv:0910.2052](https://arxiv.org/abs/0910.2052)
- **Goldston–Trudgian–Turnage-Butterbaugh.** They state the same h(c) "where… y = T^{1−δ} for some small δ > 0. Montgomery and Odlyzko proved that if h(c) > 1 for all sufficiently large T for some choice of a_k's, c, and a small δ, then assuming RH we have µ ≤ c."
  - Limitations: Conrey–Ghosh–Gonek showed "h(c) < 1 if c < 1/2", and GTT prove "If c < 0.5042, then h(c) < 1" (so the method cannot reach µ < 0.5042).
  - Current records: µ ≤ 0.515396 (Preobrazhenskiĭ) and λ ≥ 3.18 (Bui–Milinovich).
  — [arXiv:2201.10676](https://arxiv.org/abs/2201.10676)
- **Inoue–Kobayashi–Toma, resonance version.**
  - Montgomery–Odlyzko's functional, in their notation: "For a large real number T and L ≤ T/(log T)², they studied the function τ(ξ; f) := ξ − (2/π) Re Σ_{km≤L} Λ(k)/(√k log k) · sin(πξ log k/log T) f(m) f̄(km) / Σ_{n≤L}|f(n)|²."
  - Their Proposition 3 evaluates ∫(S(t+h/2) − S(t−h/2)) |R(t)|² Φ((t−3T/2)/(T/log T)) dt with Φ(t) = e^{−t²/2}. It does so by applying an explicit formula for ∫ log ζ(½+i(t+v))V(t)dt to V_{m,n}(z) = (n/m)^{iz}Φ(…).
  - Their Lemma 3.2 is the smoothed diagonal: ∫|R(t)|²Φ(…)dt = √(2π)(T/log T)(1+O(1/T))Σ|f(n)|² for L ≤ T/(log T)².
  - "The method due to Montgomery and Odlyzko is a precursor of our approach."
  — [arXiv:2510.14309](https://arxiv.org/abs/2510.14309)
- **Goldston on Montgomery–Odlyzko.** "By a different method (on RH), Montgomery and Odlyzko [30] improved on this result and obtained the upper bound 0.5179. Conrey, Ghosh, and Gonek [5] later replaced this by 0.5172." — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Landau's formula and uniform versions.** Landau's formula reads "(for x fixed) as T → ∞, Σ_{0<γ≤T} x^ρ = −(T/2π)Λ(x) + O(log T)… Fujii [10] and independently Gonek [19] have developed uniform versions." The reference is Gonek, "An explicit formula of Landau and its applications to the theory of the zeta-function", Contemp. Math. 143 (1993) 395–413. — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Rudnick–Soundararajan at zeros.** Pearce-Crump (2026) proves RH lower bounds for Σ_{0<γ≤T}|ζ(2ρ)/ζ′(ρ)|^{2k}. He follows "the strategy of Milinovich–Ng [9], which is based on the work of Rudnick and Soundararajan", the "mollified Hölder (or Cauchy) inequality… in the discrete form used by Milinovich and Ng". He acknowledges that the k = 1 case appears in S. Sinha's 2025 Missouri PhD thesis. This is a contour method, not band-limited GW. — [arXiv:2606.12376](https://arxiv.org/abs/2606.12376)
- **Soundararajan 2009 (Annals).** "Proposition. Assume RH. Let T be large, let t ∈ [T, 2T], and let 2 ≤ x ≤ T². Let λ0 = 0.4912… For all λ ≥ λ0 we have log|ζ(½+it)| ≤ Re Σ_{n≤x} Λ(n)/(n^{½+λ/log x+it} log n) · log(x/n)/log x + ((1+λ)/2) log T/log x + O(1/log x)." — [Soundararajan, Moments of the Riemann zeta function, arXiv:math/0612106](https://arxiv.org/abs/math/0612106)

### Inferences
- **The note against Montgomery–Odlyzko.** The note's identity is a pointwise, full-window, error-free analogue of M–O's functional.
  - M–O/CGG weight the Landau form by g_c(n) = 2 sin(πc log n/log T)/(π log n), the transform of a short window of length 2πc/log T. The note's Φ̂ is evaluated at log k − log(m/n) = 0, so the weight is the constant Φ̂(0). This is the un-windowed, Landau–Gonek-type main term for Σ_{|γ|≤T}|D(γ)|² rather than for Σ_γ∫|A(γ+α)|²dα.
  - M–O/CGG/IKT need N ≤ T/(log T)² (or T^{1−δ}) and carry o(1) or O(1/T) errors. The note works at T ≥ e^{24}N with exact diagonal and prime terms. The tiny-error Gaussian diagonal of IKT's Lemma 3.2 is the smooth analogue of the note's exact Ingham/Selberg-type diagonal.
- **Bound versus optimise.** M–O optimise the Landau form (choosing a_k to make h(c) large or small). The note only bounds it, by (log N + O(1))Σb² via a Schur test plus Mertens. Sharpness check: b_n = n^{−1/2} gives ratio ≈ log N (my own computation, not from a source). The constant log N therefore cannot be improved in general, which is consistent with the note's log(T/N) main term.
- **Soundararajan's inequality.** The weight log(x/n)/log x is a triangle (Fejér) weight in log n, i.e. a band-limited kernel on the zero side. It is a band-limited explicit-formula argument, but for log|ζ| at a point, not for |A|²-weighted zero sums.

### Gaps
- I could not access Montgomery–Odlyzko's paper to confirm how GW was applied. Whether they used h(t) = |A(t)|²F±(t − τ), integrated in τ, or another arrangement is unverified. Bui–Milinovich–Ng and GTT say only "by an argument using the Guinand–Weil explicit formula".
- I found no evidence on the following prompt items:
  - Montgomery–Vaughan, Multiplicative Number Theory I (2007): no exercise on Σ_γ|Σa_n n^{−iγ}|² via the explicit formula was found.
  - Selberg's mollifier-based density of zeros on the line: no evidence it uses GW with |A|²w.
  - Heath-Brown: nothing found.
  - Rodgers: nothing found.
  - Ng's "Extreme values of ζ′(ρ)" and Milinovich–Ng IMRN 2014: not checked directly.
- The exact form of Gonek's uniform Landau formula, and the resulting asymptotic for Σ_{0<γ≤T}|A(ρ)|² with its error terms, was not verified here. It is presumably covered by the Landau–Gonek track.

---

## 4. The choice of minorant: Beurling–Selberg minorants of intervals, Vaaler, Littmann, Holt–Vaaler, Gonçalves; minorants that vanish at the origin; polynomial-times-sinc^k constructions

### Takeaway
Two standard ingredients exist. One is the band-limited minorant of an interval, either Selberg's (extremal when δ·|I| ∈ ℤ, Littmann otherwise) or the explicit "Selberg minorant" (sin πu/πu)²/(1−u²) used by Montgomery-school pair-correlation arguments. The other is the trick of controlling sign through a factor that is negative outside the interval. Optimal minorants with a vanishing condition exist (Littmann–Spanier), but vanishing at a point ia off the real axis.

I found no source for the specific Φ(r) = (r/T)²(1−(r/T)²)sinc⁶(6r/T). It reads as a non-extremal, hand-built member of the "(1−x²)·(non-negative band-limited kernel)" family, multiplied by x² to vanish at 0. This is legitimate, but it gives up the extremal constant.

### Cited Findings
- **Selberg's functions.** "Selberg [37, 39] introduced functions C(x) and c(x) with the following properties: (i) Ĉ(ξ) = ĉ(ξ) = 0 if |ξ| > δ; (ii) c(x) ≤ 1_I(x) ≤ C(x)…; (iii) ∫(C − 1_I) = ∫(1_I − c) = δ^{−1}. Furthermore… Selberg's functions minimize the integrals… if and only if δ·length(I) ∈ ℤ. If δ·length(I) ∉ ℤ, then the extremal functions have been found by Littmann." "Originally, Selberg was motivated to construct his one dimensional extremal functions to prove a sharp form of the large sieve." For the higher-dimensional box problem, "Holt and Vaaler initiate the study". — [Carruth–Elkies–Gonçalves–Kelly, The Beurling–Selberg box minorant problem, arXiv:1702.04579](https://arxiv.org/abs/1702.04579)
- **The explicit Selberg minorant.** "Consider the Fourier pair h(u) = (sin πu/πu)² · 1/(1 − u²), ĥ(α) = max(1 − |α| + sin 2π|α|/(2π), 0), where h(u) is the Selberg minorant of the characteristic function of the interval [−1, 1] in the class of functions with Fourier transforms with support in [−1, 1]." Used with Montgomery's F(α), it gives lim inf (γ_{n+1}−γ_n) log γ_n/2π ≤ 0.6072… on RH. — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **The Fejér kernel.** Montgomery's simple-zeros argument uses the Fejér pair k(u) = (sin πλu/πλu)², k̂(α) = (1/λ)max(1−|α|/λ, 0). — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Vaaler 1985 and Montgomery 1978** are the standard references for proofs of the Beurling–Selberg majorant/minorant lemma used with GW. Goldston–Gonek: "For a proof of this lemma, see H. L. Montgomery [3] and J. D. Vaaler [6]. The slightly less familiar property iv) [decay off the interval] is obtained from Lemma 5 of [6]." — [Goldston–Gonek, arXiv:math/0511092](https://arxiv.org/abs/math/0511092)
- **Optimal functions with a vanishing condition.** Littmann–Spanier (Constr. Approx. 42 (2015) 209) determine "the optimal majorant M⁺ and minorant M⁻ of exponential type for the truncation of x ↦ (x²+a²)^{−1} with respect to general de Branges measures… As an application we determine the optimal majorant and minorant for the Heaviside function that vanish at a fixed point α = ia on the imaginary axis… the difference of majorant and minorant has integral value (πa − tanh(πa))^{−1}πa." — [arXiv:1311.1157](https://arxiv.org/abs/1311.1157)
- **Weight vanishing at 0.** CCLM's optimisation measure 1 − (sin πx/πx)² vanishes to second order at 0. Their extremal majorants and minorants of χ_[−β,β] are optimal for this measure, which suppresses the origin. — [arXiv:1406.5462](https://arxiv.org/abs/1406.5462)
- **Optimal one-sided band-limited approximation in RKHS/de Branges frameworks** for the explicit formula: Carneiro–Chandee–Milinovich (Gaussian subordination; the odd function arctan(1/x) − x/(1+x²)), Chandee–Soundararajan (log((4+x²)/x²)), and Carneiro–Chirre–Milinovich (L¹-optimal band-limited majorants with explicit Fourier transforms). — [arXiv:1309.1526](https://arxiv.org/abs/1309.1526); [arXiv:0908.2008](https://arxiv.org/abs/0908.2008); [arXiv:1710.10362](https://arxiv.org/abs/1710.10362)

### Inferences
- **Sign control in Φ.** In Φ(r) = (r/T)²(1−(r/T)²)sinc⁶(6r/T) the factor (1−x²) controls the sign. This is the same mechanism as the factor 1/(1−u²) in Selberg's minorant, but polynomial rather than rational. The non-negative kernel sinc⁶ caps Φ at ¼ = max x²(1−x²) on [−1,1] and gives exponential type 36/T. Each sinc(6r/T) contributes type 6/T, and the polynomial factor does not enlarge the support.
- **Why vanish at 0.** The factor x² kills the region |γ| ≪ T, where log|t| is small and the archimedean weight is not ≈ log T. The pole term h(±i/2) becomes O(N/T²)-small relative to the main term (my estimate, not sourced). The closest literature analogue of building a vanishing condition into a band-limited extremal problem is Littmann–Spanier, with the zero at ia. The note does not claim extremality, and none is in the literature for this exact shape.
- **Possible sharpening.** The constant 1/100 could likely be improved by replacing Φ with a de Branges/RKHS-optimal minorant of 1_[−T,T] under a vanishing constraint at 0, in the style of CCLM or Carneiro–Chirre–Milinovich. This is an inference, not checked.

### Gaps
- No source found for x²(1−x²)·sinc^k minorants. The literature on "polynomial × sinc^k" ansätze in Fourier-optimisation numerics (e.g. the SDP work of Chirre–Gonçalves–de Laat) was not checked in detail.
- Holt–Vaaler (Duke Math. J. 83 (1996)) and Gonçalves' de Branges interpolation papers were not read directly. Their roles here are known only from secondary mentions (CEGK).
- Ingham's 1936 inequality (Math. Z. 41) and the Selberg/Montgomery–Vaughan lower-bound ("dual large sieve") inequalities were not verified from primary sources. AMS and Project Euclid PDFs were blocked by bot checks.

---

## 5. Is the specific combination (explicit formula + band-limited minorant with transform support < 1/(2N), making the Landau off-diagonal term exact) stated for discrete mean values of Dirichlet polynomials at zeros? Who first observed that compact Fourier support makes off-diagonal terms exact?

### Takeaway
I found no paper that states the combination: GW applied to |D(t)|²Φ(t) with supp Φ̂ smaller than the minimal gap 1/(2N) between log(m/n) and log k, so that both the diagonal ∫|D|²Φ = Φ̂(0)Σb² and the prime side (Landau's form) are exact, giving an explicit RH lower bound for Σ_{|γ|≤T}|D(γ)|² in the linear range T ≫ N.

The components all have clear predecessors:
- **GW plus band-limited majorants/minorants:** Montgomery–Odlyzko 1984, then Goldston–Gonek 2007 and the Carneiro–Chandee–Milinovich school.
- **Dirichlet-polynomial weights in GW, with the Landau form as the off-diagonal term:** Montgomery–Odlyzko 1984, and in Gonek-lemma form Conrey–Ghosh–Gonek 1984.
- **"Support below the arithmetic spacing ⇒ only multiplicatively matched terms survive, exactly":** Selberg's band-limited proof of the large sieve; Montgomery's [−1,1] principle; Rudnick–Sarnak's and Hughes–Rudnick's restricted-support n-level and moment computations, where the argument "log(M/N) = log(1+u/N) ≫ 1/N ⇒ M = N" appears verbatim.

What looks new is the assembly into an exact, error-free, explicit-constant sampling inequality at the zeros in the linear range T ≥ e^{24}N, with general coefficients.

### Cited Findings
- **Hughes–Rudnick 2002 (C. R. Acad. Sci. Paris 335, 667–670).**
  - Setup: test functions with f̂ smooth and compactly supported, an averaging weight w ≥ 0 "with ŵ compactly supported", and "will not assume the Riemann Hypothesis".
  - Theorem 1.1: if supp f̂ ⊆ (−2a/m, 2a/m) with H = T^a, "the first m moments of N_f converge… to those of a Gaussian", with variance σ_f² = ∫ min(|u|,1) f̂(u)² du.
  - Mean: "Since ŵ has compact support, and the prime powers n are at least 2, the summands vanish once H is larger than a certain constant."
  - Moments: "Since ŵ has compact support, in order to get a nonzero contribution we need |Σ ε_j log n_j| ≪ 1/H. Set M = Π_{ε_j=+1} n_j and N = Π_{ε_j=−1} n_j. If M ≠ N… 1/H ≫ log(M/N) = log(1 + u/N) ≫ 1/N… contradiction. Therefore M = N."
  — [arXiv:math/0208220](https://arxiv.org/abs/math/0208220)
- **Fazzari–Gerspach–Minelli (2025).** They combine Selberg's CLT with Hughes–Rudnick linear statistics and show that a complex CLT holds when the Fourier support of the test function is sufficiently small (per search summary; not read in full). — [arXiv:2507.04150](https://arxiv.org/abs/2507.04150)
- **Rudnick–Sarnak (Duke Math. J. 81 (1996), DOI 10.1215/S0012-7094-96-08115-6).** Their n-level correlation theorem for cuspidal GL_m L-functions is proved for test functions whose Fourier transform "is supported in Σ_j |ξ_j| < 2/m" (assuming m ≤ 3 or Hypothesis H). This is as restated in a 2020 exposition; the original was not consulted. — [Exposition, arXiv:2002.00595](https://arxiv.org/abs/2002.00595); [MaRDI record](https://portal.mardi4nfdi.de/wiki/Publication:1919610)
- **Montgomery 1973.** "We can evaluate sums over differences of zeros on the class of functions whose Fourier transforms are supported in [−1, 1]." — [Goldston, arXiv:math/0412313](https://arxiv.org/abs/math/0412313)
- **Selberg's large sieve.** "Originally, Selberg was motivated to construct his one dimensional extremal functions to prove a sharp form of the large sieve." The functions have Ĉ = ĉ = 0 for |ξ| > δ. — [arXiv:1702.04579](https://arxiv.org/abs/1702.04579)
- **The same template in Goldston–Gonek.** Their prime sum is restricted to n < e^{2πδ} "since F̂ vanishes for |x| ≥ δ", which is the same compact-support truncation, but there the support is used only to make the sum short. — [arXiv:math/0511092](https://arxiv.org/abs/math/0511092)
- **CMS.** They apply GW to f(z)a^{iz} with f band-limited, a single-frequency version of the note's (m/n)^{iz}Φ(z) terms. — [arXiv:1708.04122](https://arxiv.org/abs/1708.04122)
- **Weil positivity with small support (related, different side of the duality).**
  - Yoshida, "On Hermitian forms attached to zeta functions" (Adv. Stud. Pure Math. 21 (1992) 281–325), reduces RH to non-degeneracy of a Hermitian form. He reports positive definiteness on a restricted space for small values of the support parameter (per search summary of the Project Euclid record). — [Project Euclid](https://projecteuclid.org/ebooks/advanced-studies-in-pure-mathematics/Zeta-Functions-in-Geometry/chapter/On-Hermitian-Forms-attached-to-Zeta-Functions/10.2969/aspm/02110281.pdf)
  - A seminar abstract says "earlier work by Yoshida and Bombieri proves positivity of the Weil functional for test functions with small support" (secondary source). — [Bryn Mawr NT seminar abstract](https://www.brynmawr.edu/sites/default/files/migrated-files/NTSeminarAbstract_11.19.15_000.pdf)
  - Connes–Consani give "a potential conceptual reason for the positivity of the Weil functional… the simplest case of the single archimedean place… in terms of prolate spheroidal wave functions". — [arXiv:2006.13771](https://arxiv.org/abs/2006.13771)

### Inferences
- **Novelty, as far as this search reaches.** The note can claim novelty for:
  - (i) using the support condition supp Φ̂ ⊂ [−36/T, 36/T] with 36/T < 1/(2N) to make GW's prime side equal to Φ̂(0)·2Σ_k Λ(k)k^{−1/2}Σ_{jk≤N}b_j b_{jk} exactly;
  - (ii) pairing this with the exact Ingham/Selberg-type diagonal ∫|D|²Φ = Φ̂(0)Σb²;
  - (iii) obtaining a fully explicit RH lower bound Σ_{|γ|≤T}|D(γ)|² ≥ (T/100)Σb² for T ≥ e^{24}N, uniform in the coefficients.

  The analogous M–O/CGG/IKT evaluations are asymptotic (o(1) or O(1/T)), restricted to N ≤ T/(log T)² or T^{1−δ}, and windowed (they sum ∫|A(γ+α)|²dα over short windows). Montgomery's line is two-level.
- **Suggested citations.**
  - GW: Iwaniec–Kowalski Thm 5.12, in the form of Goldston–Gonek Lemma 1 and CMS Lemma 6.
  - Band-limited extremal functions with GW: Montgomery–Odlyzko 1984; Goldston–Gonek 2007; Carneiro–Chandee–Milinovich 2013/2015; Chandee–Soundararajan 2011; Carneiro–Chirre–Milinovich 2019; Carneiro–Milinovich–Soundararajan 2019.
  - Dirichlet-polynomial weights and the Landau form at zeros: Montgomery–Odlyzko 1984; Conrey–Ghosh–Gonek 1984; Bui–Milinovich–Ng 2010; Goldston–Trudgian–Turnage-Butterbaugh 2023; Inoue–Kobayashi–Toma 2025/26; for the un-windowed sum, Landau 1911 and Gonek 1993.
  - "Support below spacing ⇒ exact diagonal": Selberg (large sieve; Montgomery 1978, Vaaler 1985); Montgomery 1973; Rudnick–Sarnak 1996; Hughes–Rudnick 2002.
  - Minorant design: Selberg's minorant (sin πu/πu)²/(1−u²); Littmann–Spanier (vanishing condition); CCLM (measure vanishing at 0).
- **Weil-positivity framing.** The note can be read as a quantitative, localized Weil positivity for test functions built from a discrete measure Σb_nδ_{log n}. Yoshida/Bombieri-type small-support positivity concerns the opposite regime (support in a small multiplicative neighbourhood of 1, where the prime terms vanish entirely). In the note the support is a union of tiny intervals around log(m/n), and the prime terms reduce exactly to the matched pairs kn = m. This framing is my interpretation, not a cited statement.

### Gaps
- I cannot name the first person to observe that compact Fourier support makes off-diagonal terms exact. The earliest instances found are Selberg's large sieve via band-limited majorants (date not verified; communicated via Montgomery 1978 and Vaaler 1985) and Montgomery 1973. Ingham 1936 is a plausible earlier precursor, but its role is unverified.
- Not consulted directly: Rudnick–Sarnak 1996, Iwaniec–Luo–Sarnak 2000 (Publ. IHÉS 91), Katz–Sarnak 1999 (Bull. AMS 36), and Hughes–Rudnick's 2003 papers on low-lying zeros and mock-Gaussian behaviour. Their support statements come from expositions or secondary abstracts.
- Bombieri's paper on Weil's quadratic functional (Rend. Lincei 2000) was not located. The small-support positivity statement attributed to it is secondary only.
- Searches for an explicit statement of "Σ_γ |Σ_{n≤N} b_n n^{iγ}|² ≥ cT Σb_n² via band-limited Guinand–Weil" returned nothing. That is evidence of absence only within the indexed sources searched (arXiv metadata, general web search). It is not proof of novelty.
