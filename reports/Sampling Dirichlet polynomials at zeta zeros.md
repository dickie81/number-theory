# Sampling at zeta zeros reaches the linear range

**`BallCutoff.sampling_rh` does not appear in the literature, in this form or a stronger one. The only relatives are weaker: they stop at polynomial length N ≤ T/log²T, or they average each zero over a window.** The closest is Theorem 3.1 of Bui–Florea–Milinovich (Bull. LMS 2024), which rests on Gonek's uniform version of Landau's formula. Combined with Conrey–Ghosh–Gonek's AM–GM bound on the Landau form, it gives under RH a lower bound of the stronger shape (T/π)(log(T/N) − O(1))·Σb_n², but only for N ≤ cT/log²T and with inexplicit constants. At T ≍ N its error term exceeds the diagonal by a factor ≍ log T, and no published statement covers T between C·N and N·log²N ([Bui–Florea–Milinovich](https://arxiv.org/abs/2310.03949)). The Montgomery–Odlyzko / Conrey–Ghosh–Gonek method is uniform in the coefficients, but it smears each zero over about ±3 mean spacings and has the same length limit ([Bui–Milinovich–Ng](https://arxiv.org/abs/0910.2052)). What is genuinely new:

- the linear range T ≥ e²⁴N;
- a pointwise sharp cutoff;
- explicit constants;
- the mechanism: Fourier support 36/T below the 1/(2N) frequency separation makes the diagonal and Landau's form exact.

Each ingredient has a precedent; their assembly does not. The range is necessary up to its constant: the inequality fails for T ≤ (2π − ε)N. At T = CN the zeros exceed the Nyquist density of the polynomial only additively, by (1/2π)log(C/2π) ≈ 3.5 at C = e²⁴, which is the near-critical regime where Beurling–Landau theory decides nothing. The log-free constant is the right order for bounded T/N. The true constant should grow like (1/π)log(T/N); the proof itself already yields about 0.0022·T·log(T/N), and that 140-fold loss is exactly the mass the minorant Φ gives up. The corollary λ_N ≥ 1/(200e²⁴N) appears to be the first polynomial lower bound for the smallest eigenvalue of any RH-related Gram form. Nyman–Beurling lower bounds are ineffective lim infs for a single distance, and Weil forms on windows have super-exponentially small eigenvalues ([Burnol](https://arxiv.org/abs/math/0103058); [Connes–Consani](https://arxiv.org/abs/2106.01715)).

## Every published mean value over the zeros stops at N ≤ T/log²T

The ancestor of every discrete mean value over the zeros is Landau's formula. For fixed x > 1, Σ_{0<γ≤T} x^ρ = −(T/2π)Λ(x) + O(log T) ([Durkan–Hughes–Pearce-Crump](https://arxiv.org/abs/2601.18025)). Gonek made it uniform, in papers of 1985 (Austin proceedings) and 1993 (Contemp. Math. 143). Without RH, for all x, T > 1,

**Σ_{0<γ≤T} x^ρ = −(T/2π)Λ(x) + O(x log(2xT) log log 3x) + O(log x · min(T, x/⟨x⟩)) + O(log 2T · min(T, 1/log x)),**

where ⟨x⟩ is the distance from x to the nearest prime power other than x ([Milinovich, Lemma 4.1](https://arxiv.org/abs/0806.0786)). Five later papers reproduce this identically. Bui–Florea–Milinovich cite it as Theorem 1 of the 1993 paper ([BFM, Lemma 3.2](https://arxiv.org/abs/2310.03949)), and Fujii added lower-order terms ([DHP](https://arxiv.org/abs/2601.18025)). Milinovich and Ng summarise the field in one sentence: every evaluation of Σ_{0<γ<T}|A(ρ)|² with A of length ξ ≤ T "either makes use of the Guinand–Weil explicit formula or of Gonek's uniform version of Landau's formula" ([Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)).

The cleanest general consequence is **Bui–Florea–Milinovich's Theorem 3.1**: assuming RH, for x ≥ 2, T > 1 and any complex a_n,

Σ_{0<γ≤T} |Σ_{n≤x} a_n n^{−ρ}|² = N(T)·Σ|a_n|²/n − (T/π)·Re Σ_{kn≤x} a_{kn} ā_n Λ(k)/(kn) + O(x·log²(xT)·Σ|a_n|²/n).

The authors call it "of independent interest" and "similar in flavor to the Montgomery–Vaughan mean-value theorem for continuous averages". They use it only for upper bounds on negative moments of ζ′(ρ) ([BFM](https://arxiv.org/abs/2310.03949)).

In the theorem's normalisation, put a_n = n·x_n and b_n = x_n√n. Then Σ|a_n|²/n = Σx_n²n = Σb_n², and the cross term becomes b_m b̄_{mk} Λ(k)/√k. For real coefficients the sum over |γ| ≤ T is twice the sum over 0 < γ ≤ T. So `sampling_rh` is equivalent to Σ_{0<γ≤T}|Σ b_n n^{−iγ}|² ≥ (T/200)Σb_n², a statement directly comparable with BFM. The other explicit statements are all shorter in range, specialised in coefficients, or upper bounds only.

| Result | Hypothesis | Admissible length | What it controls | Information at T = C·N |
|---|---|---|---|---|
| Landau (1911) | none | x fixed | Σ x^ρ | none |
| Gonek (1985, 1993) | none | uniform in x, T | Σ x^ρ with the errors above | errors exceed the main term |
| [Ng 2008, Prop. 4(i)](https://arxiv.org/abs/0706.1765) | RH, x_n ≪ T^ε | N = T^θ, θ < 1 | asymptotic, error o(T) | excluded |
| [Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf) | RH | ξ = T^ϑ, ϑ < 1, Möbius coefficients only | (3/π³)(ϑ + ϑ²)T log²T + O(T log T) | excluded |
| [Milinovich 2010, Lemma 4.2](https://arxiv.org/abs/0806.0786) | RH | ξ ≤ T/log T | upper bound only | upper bound only |
| [Çiçek 2021, Lemma 3.1](https://arxiv.org/abs/2007.10533) | RH | M, N ≤ T | asymptotic with N log²T errors | errors dominate |
| [BFM 2024, Thm 3.1](https://arxiv.org/abs/2310.03949) | RH | any x ≥ 2, T > 1 | asymptotic, error O(x log²(xT)Σ\|a\|²/n) | error ÷ diagonal ≍ log T / C |
| BFM + AM–GM (derived in the notes) | RH | N ≤ cT/log²T | lower bound ≍ T log(T/N)·Σb² | out of range |
| [Montgomery–Odlyzko / CGG / BMN](https://arxiv.org/abs/0910.2052) | RH | K = T/log²T (or T^{1−δ}) | window-averaged sum, uniform in coefficients | excluded |
| Twisted sums ([Bui–Heath-Brown](https://arxiv.org/abs/1302.5018), [Benli–Elma–Ng](https://arxiv.org/abs/2311.13554)) | RH | below T^{1/2} | Σ ζ′(ρ)\|A(ρ)\|², Σ ζ(ρ+α)X(ρ)Y(1−ρ) | excluded |
| `BallCutoff.sampling_rh` | RH | T ≥ e²⁴N | pointwise lower bound, explicit | (T/100)·Σb² |

**What these give at T ≍ N.** Take T = CN. BFM's error term is ≍ (T/C)·log²T·Σb², while the diagonal N(T)·Σb² is ≍ (T/2π)·log T·Σb². The error is larger by a factor ≍ log T/C, so **Theorem 3.1 says nothing anywhere in T ∈ [CN, N log N]**. It is an honest asymptotic only when N = o(T/log T) and the diagonal is not cancelled.

The main term itself is still informative. A Schur/AM–GM bound with Mertens' estimate gives |2 Re Σ b_m b̄_{mk}Λ(k)/√k| ≤ (log N + O(1))·Σb². The main term is therefore at least (T/2π)(log(T/2πN) − O(1))·Σb². Equality is approached by the ζ-like coefficients b_n = n^{−1/2}, so the Landau term can cancel all of the diagonal except a factor log(T/N). This computation is in the research notes, not in any source. Kirila flags the same danger: the secondary term is "possibly of the same order as that of the first term … not positive" ([Kirila](https://arxiv.org/abs/1804.08826)).

Putting the pieces together gives, under RH, Σ_{|γ|≤T}|D(γ)|² ≥ (T/π)(log(T/N) − O(1))·Σb² − O(N log²T·Σb²). This bound is non-trivial once N ≤ cT/log²T. In that sub-range it is **stronger than `sampling_rh` in size but inexplicit, and holds only for T large**. BFM never state it; it is a two-line consequence of their theorem.

The obstruction at T ≍ N is structural, not bookkeeping. Radziwiłł quotes a Ford–Zaharescu refinement in which ratios m/n lying within ≍ 1/T of a prime power produce a "near-miss" term as large as the exact Landau term. When T ≍ N, every n has such partners ([Radziwiłł, Lemma 8](https://arxiv.org/abs/1301.3232)). Durkan–Hughes–Pearce-Crump record that a heuristic using a Dirichlet polynomial of length ≍ t "gives the correct main term … but with an error term that dominates the main term" ([DHP](https://arxiv.org/abs/2601.18025)). **No statement found covers T ∈ [CN, N·log²N]**, and that interval contains the whole regime of `sampling_rh` with T/N bounded.

## Montgomery–Odlyzko comes closest, but samples through windows

Before BallCutoff, one argument applied the explicit formula to a Dirichlet-polynomial weight and obtained a bound uniform in the coefficients: Montgomery and Odlyzko's method for gaps between zeros (Budapest 1981, published 1984). Under RH, with K = T(log T)^{−2}, they study

h(c) = c − Re Σ_{nk≤K} a_k ā_{nk} g_c(n)Λ(n)n^{−1/2} / Σ|a_k|², with g_c(n) = 2 sin(πc log n/log T)/(π log n).

"By an argument using the Guinand–Weil explicit formula" they show that h(c) < 1 forces gaps of at least c mean spacings, and that h(c) > 1 forces gaps of at most c ([Bui–Milinovich–Ng](https://arxiv.org/abs/0910.2052)). Conrey, Ghosh and Gonek (1984) recast this as a comparison between the zeros and the integral. Put M₁ = ∫_T^{2T}|A|² and M₂(c) = ∫_{|α|≤πc/log T} Σ_{T≤γ≤2T}|A(γ+α)|² dα. Then **M₂(c)/M₁ = h(c) + o(1)** ([BMN](https://arxiv.org/abs/0910.2052)). Goldston–Trudgian–Turnage-Butterbaugh state the same functional with length y = T^{1−δ} ([GTT](https://arxiv.org/abs/2201.10676)).

The method's barriers are sampling theorems in disguise. As BMN and GTT report it, Conrey–Ghosh–Gonek showed for every choice of coefficients that h(c) < 1 when c < 1/2 and h(c) > 1 when c ≥ 6.2. GTT sharpen the first barrier to c < 0.5042 and record improvements of the second to 3.74, and numerically 3.6747 ([GTT](https://arxiv.org/abs/2201.10676)).

Read through M₂/M₁, "h(c) > 1 for c ≥ 6.2" makes a sampling claim. Take any A of length at most T/log²T and smear each zero between T and 2T over a window of ±3.1 mean spacings. The smeared zeros then carry at least the continuous mean square ∫_T^{2T}|A|². That is **a coefficient-uniform sampling inequality, but asymptotic, windowed, and confined to N ≤ T/log²T**.

The CGG proof of the c < 1/2 barrier rests on an AM–GM bound for the Landau form ([GTT](https://arxiv.org/abs/2201.10676)). That is the same device as the project's `BallDensity.landau_le`. The test polynomials of this literature approximate ζ^r with d_r(k)k^{−1/2} coefficients and are chosen to be "small near the zeros" ([BMN](https://arxiv.org/abs/0910.2052)). They are exactly the coefficients for which the Landau term cancels the diagonal.

Against this background, `sampling_rh` is the un-windowed, error-free counterpart of the Montgomery–Odlyzko functional. There, the Landau form is weighted by g_c(n), the transform of a window of width 2πc/log T. In BallCutoff, Φ̂ is evaluated only at log k − log(m/n) = 0, so the weight is the constant Φ̂(0). The result is the plain Landau–Gonek main term for Σ_{|γ|≤T}|D(γ)|², with no o(1), at lengths up to T/e²⁴ rather than T/log²T. Montgomery and Odlyzko optimise the Landau form over the coefficients; BallCutoff only bounds it. The 2026 resonance version of Inoue–Kobayashi–Toma, which calls the method "a precursor of our approach", likewise needs L ≤ T/(log T)² for its Gaussian-smoothed diagonal ([Inoue–Kobayashi–Toma](https://arxiv.org/abs/2510.14309)).

## The explicit-formula toolkit is old; support below 1/(2N) is the new move

Every analytic component of the proof has a named predecessor.

The explicit formula in the form used has four features: h analytic in a strip with compactly supported transform, pole terms h(±i/2), a Γ′/Γ archimedean term, and a prime sum over Λ(n)n^{−1/2}ĥ(±log n/2π). This is Goldston–Gonek's Lemma 1, which they call "a specialization of Theorem 5.12" of Iwaniec–Kowalski; Carneiro–Milinovich–Soundararajan cite it the same way ([Goldston–Gonek](https://arxiv.org/abs/math/0511092); [CMS](https://arxiv.org/abs/1708.04122)).

Pairing that formula with band-limited minorants and majorants F± of 1_[−L,L], where F̂± vanishes for |x| ≥ δ, goes back to Montgomery–Odlyzko. Goldston–Gonek's Lemma 2 "is essentially Lemma 2 from" their paper, with proofs credited to Montgomery 1978 and Vaaler 1985 ([Goldston–Gonek](https://arxiv.org/abs/math/0511092)).

The Carneiro–Chandee–Milinovich school turned this into an optimisation programme. Its results include:
- |S(t)| ≤ (¼ + o(1)) log t/log log t on RH ([Carneiro–Chandee–Milinovich](https://arxiv.org/abs/1309.1526));
- the optimal minorant of log((4+x²)/x²) for Littlewood's bound ([Chandee–Soundararajan](https://arxiv.org/abs/0908.2008));
- pair-correlation bounds through reproducing-kernel spaces ([CCLM](https://arxiv.org/abs/1406.5462)).

The nearest single test function is Carneiro–Milinovich–Soundararajan's h(z) = f(z)a^{iz}: a band-limited function times one Dirichlet monomial. They use it to prove that on RH every interval [x, x + (22/25)√x log x] contains a prime ([CMS](https://arxiv.org/abs/1708.04122)).

BallCutoff departs from this school in four ways, and the novelty lies in them:
1. **The test function.** |D|²Φ superposes N² modulated band-limited functions (m/n)^{iz}Φ(z); CMS's test function is the one-term case.
2. **The support.** It is tuned to the arithmetic separation of {log(m/n)} from {log k}, not to log log t.
3. **The prime side.** As a result it is not bounded trivially: it **equals Landau's form exactly**.
4. **The pole term.** It is controlled by vanishing to second order at 0, not by exponential type alone.

The principle that compact Fourier support isolates multiplicatively matched terms is itself classical:
- Montgomery's pair-correlation method "can evaluate sums over differences of zeros on the class of functions whose Fourier transforms are supported in [−1, 1]" ([Goldston's notes](https://arxiv.org/abs/math/0412313)).
- Selberg built his band-limited extremal functions "to prove a sharp form of the large sieve" ([Carruth–Elkies–Gonçalves–Kelly](https://arxiv.org/abs/1702.04579)).
- Hughes and Rudnick spell out the separation argument behind `BallDensity.sep_log` almost word for word: "we need |Σ ε_j log n_j| ≪ 1/H … 1/H ≫ log(M/N) = log(1 + u/N) ≫ 1/N … Therefore M = N" ([Hughes–Rudnick](https://arxiv.org/abs/math/0208220)).

**The minorant Φ(r) = (r/T)²(1 − (r/T)²)sinc⁶(6r/T) has no precedent found.** Its sign mechanism is a factor that is negative outside [−T, T], times a non-negative band-limited kernel. That is the polynomial analogue of the 1/(1 − u²) in Selberg's minorant (sin πu/πu)²/(1 − u²), whose transform is max(1 − |α| + sin 2π|α|/2π, 0) ([Goldston's notes](https://arxiv.org/abs/math/0412313)). The closest extremal theory with a built-in zero is Littmann and Spanier's: they find the optimal majorants and minorants that vanish at a point ia on the imaginary axis ([Littmann–Spanier](https://arxiv.org/abs/1311.1157)). Carneiro–Chandee–Littmann–Milinovich optimise against the measure 1 − (sin πx/πx)², which vanishes to second order at 0 ([CCLM](https://arxiv.org/abs/1406.5462)).

As Weil positivity, BallCutoff is a localized, quantitative instance:
- **Yoshida- and Bombieri-type positivity** concerns support near the identity, where the prime terms vanish entirely ([Connes–Consani 2021](https://arxiv.org/abs/2006.13771)).
- **BallCutoff** works with support on a union of tiny intervals around log(m/n), and the prime terms reduce exactly to the matched pairs kn = m.

## Sampling theory explains the 2πN crossover but cannot supply the bound

No paper found calls the zeta zeros a sampling set, frame or Marcinkiewicz–Zygmund family for Dirichlet polynomials. Searches pairing "sampling", "frame", "Marcinkiewicz–Zygmund", "Beurling density" or "Paley–Wiener" with zeta zeros returned only Beurling-zeta and Nyman–Beurling papers. A full-text search of Saksman and Seip's problem list for Dirichlet series finds the zeros nowhere as sampling points ([Saksman–Seip](https://arxiv.org/abs/1601.01616)).

Density theory explains the shape of `sampling_rh`. Four classical results set the frame:
- **Beurling:** a separated Λ samples the Bernstein space B_σ if and only if its lower uniform density exceeds σ/π.
- **Landau (1967):** density at least the Nyquist rate is necessary for any bounded spectrum ([Olevskii–Ulanovskii](https://arxiv.org/abs/1512.01437)).
- **Disconnected spectra:** no density condition is sufficient ([Olevskii–Ulanovskii](https://arxiv.org/abs/1512.01437)).
- **Critical density (Ortega-Cerdà–Seip):** sampling depends on whether the counting function deviates from ℤ by at least a logarithm. Landau's inequality n_Λ(b) − n_Λ(a) ≥ b − a − A log⁺(b − a) − B "is best possible" ([Ortega-Cerdà–Seip](https://arxiv.org/abs/math/0005092)).

Now the bookkeeping, which is the research notes' derivation. For a polynomial of length N the frequencies log n fill [0, log N], so the Nyquist density is (log N)/2π. The ordinates near height t have density (1/2π)log(t/2π). The two cross at t = 2πN; below that height the zeros are sparser than Nyquist. At T = CN the zeros exceed Nyquist by **(1/2π)log(C/2π), an additive constant (≈ 3.53 at C = e²⁴) whose ratio to the Nyquist density tends to 0 as N grows**. A multiplicative excess, a density ratio of 1 + θ, would require T = N^{1+θ}. So `sampling_rh` sits in the near-critical regime where density alone decides nothing. The project's hypothesis `SamplingAtZeros c C θ` splits along exactly this line between θ = 0 and θ > 0.

Two features of the zeros rule out the generic arguments. First, density never fixes frame constants, and a long gap can host a band-limited function concentrated inside it. Under RH there are infinitely many gaps longer than 3.18 mean spacings ([Bui–Milinovich](https://arxiv.org/abs/1410.3635)). At T = e²⁴N such a gap exceeds the Nyquist spacing 2π/log N once log N > 10.2 (the notes' computation). Second, Marcinkiewicz–Zygmund inequalities for scattered points grew out of irregular-sampling theory ([Gröchenig](https://arxiv.org/abs/1909.07752)), whose classical lower bounds assume every gap is short. The Wirtinger inequalities of that tradition are precisely the tool Hall, Bredberg and Bui–Milinovich use to prove that large gaps exist ([Bui–Milinovich](https://arxiv.org/abs/1410.3635)). The project's own `BallSampling`, which needs a zero in every cell of length 1/(1 + log N), follows this route, which is why it needs a gap hypothesis. The explicit-formula minorant replaces that hypothesis with the arithmetic of the zeros.

The upper side is routine:
- Iwaniec–Kowalski's large sieve gives (T + 2πN)·log(2N)·‖a‖² for 1-spaced points, as restated in [Harrison's notes](https://warwick.ac.uk/fac/sci/maths/people/staff/josephharrison/dirichlet_polynomials_week_4_notes.pdf).
- Milinovich's RH bound covers lengths up to T/log T ([Milinovich](https://arxiv.org/abs/0806.0786)).
- BFM plus the AM–GM bound gives ≲ (T/π)(log T + log N)‖b‖² + O(N log²T·‖b‖²).

**The novelty is on the lower side only.**

The continuous analogues show that 2πN is the natural crossover:
- **Montgomery's two-sided theorem**, (T − 2πN)‖a‖² ≤ ∫_0^T|D|² ≤ (T + 2πN)‖a‖², is restated from *Ten Lectures* §7.2 in [Harrison's notes](https://warwick.ac.uk/fac/sci/maths/people/staff/josephharrison/dirichlet_polynomials_week_4_notes.pdf).
- **Ingham's inverse inequality** holds on intervals longer than 2π divided by the frequency gap, which is ≈ 1/N here ([Jaming–Komornik](https://arxiv.org/abs/1903.07804)).

By the Montgomery–Vaughan theorem, ∫_{−T}^{T}|D|² = 2T‖b‖²(1 + O(e^{−24})) for T ≥ e²⁴N. So `sampling_rh` is equivalent, up to that factor, to the **unweighted Marcinkiewicz–Zygmund inequality Σ_{|γ|≤T}|D(γ)|² ≥ (1/200)·∫_{−T}^{T}|D|²**. Measured against the spacing-weighted sum, the lower constant is ≍ 1/log T. The next section shows that this loss is unavoidable when T/N is bounded.

In the Hilbert-space theory of Dirichlet series, the closest object is the dual problem. Olsen and Saksman prove that {n^{±it}/√n} is a frame for L²(I), with lower bound decaying like |I|^{−c|I|}, and remark that "explicit bounds for non-trivial frames are difficult to obtain" ([Olsen–Saksman](https://arxiv.org/abs/0907.2708)).

## The threshold lies between 2πN and e²⁴N, and the constant should grow with log(T/N)

**The hypothesis T ≥ CN cannot be dropped, and C cannot go below 2π.** Take x_n = 1/n, so b_n = n^{−1/2}. Titchmarsh's Theorem 4.11, the Hardy–Littlewood approximation, gives ζ(s) = Σ_{n≤x}n^{−s} − x^{1−s}/(1−s) + O(x^{−σ}) for |t| ≤ 2πx/C′ with C′ > 1 (quoted in [arXiv:1203.2242](https://arxiv.org/abs/1203.2242), via a search summary). At every zero below (2π − ε)N it therefore forces Σ_{n≤N}n^{−ρ} = N^{1−ρ}/(1−ρ) + O(N^{−1/2}). The left side of the inequality is then O(N·Σ_ρ|ρ|^{−2}) = O(N), while the right side is ≍ N log N. So no inequality of this form, with any fixed constant, holds for T ≤ (2π − ε)N and large N.

Arias de Reyna's explicit version makes the failure rigorous at T = N. It holds for σ ≥ 0 and 0 < t ≤ x, with error at most (29/14)x^{−σ} ([Arias de Reyna](https://arxiv.org/abs/2406.16667)). With Σ_ρ1/|ρ|² = 2 + γ − log 4π:
- at N = 10⁴ the left side is at most 941, against a right side of 979;
- at N = 10⁸ it is at most 9.24×10⁶, against 1.90×10⁷;
- the margin grows linearly, so the inequality fails at T = N for every N ≥ 10⁴.

This counterexample is the research notes' derivation, and it uses RH. **The optimal threshold therefore lies in [2πN, e²⁴N]; no source addresses where.** The project's numerics fit a crossover near 2πN ≈ 6.3N: on the minimising vectors of G_N, the sampling ratio jumps from 0.013 at T = 4N to 0.10 at T = 8N ([ball-rate.md](../formalisations/ball-rate.md)).

**For bounded T/N the log-free constant is the right order**, for the reason given in the first section. The Landau form can cancel the diagonal (T/π)log T·‖b‖² down to (T/π)(log(T/N) − O(1))·‖b‖², and ζ-like coefficients achieve this. The natural conjecture is therefore **Σ_{|γ|≤T}|D(γ)|² ≫ T·log(T/N)·‖b‖² uniformly for T ≥ C₀N**. It is rigorous wherever BFM's error term is negligible (N = T/log³T, say), but only heuristic at N ≍ T. It was not found stated anywhere and is presumably open.

That main term has a clean density reading (an interpretation, not a cited statement). The local zero density exceeds Nyquist by (1/2π)log(t/2πN) at height t. Integrated over [0, T], this gives (T/2π)(log(T/2πN) − 1), exactly the worst-case main term up to O(T). In other words, **the guaranteed sampling mass is the integrated surplus of zeros over the Nyquist count**, which is the additive density excess turned into a constant. On this heuristic the best constant at C = e²⁴ is (24 − O(1))/π: several units, not 1/100.

**The proof in the project note already has the conjectured shape.** Its final inequality reads ¼Σ_{|γ|≤T}|V_x(ρ)|² ≥ (69T/124416)(log(T/N) − log 64π − 7)Σc_n² − 0.0018TΣc_n² − O(NΣc_n²) ([ball-rate.md](../formalisations/ball-rate.md)). That amounts to Σ_{|γ|≤T}|D|² ≥ 0.0022·T·(log(T/N) − 15.5)·‖b‖² − O(N‖b‖²) for T ≥ e²⁴N. It is T·log(T/N) growth with a leading constant about 143 times below 1/π (arithmetic from the note's displayed constants).

The 143 is precisely the mass ratio of the minorant. The coefficient of log(T/N) is (2/π)∫Φ, and ∫Φ = Φ̂(0) = 69πT/62208 ≈ 0.0035T, whereas ¼·1_[−T,T] has mass T/2. Beurling–Selberg minorants with transform support δ lose only 1/δ of mass, ∫F⁻ ≥ 2L − 1/δ ([Goldston–Gonek](https://arxiv.org/abs/math/0511092)); here that is 2N out of 2T. But they do not vanish at 0, and BallCutoff needs that vanishing to control the pole and the low-height archimedean deficit. How much mass the vanishing constraint costs at support 1/(2N) is therefore the extremal problem that decides the constant. Littmann–Spanier solve a version with the zero placed at ia ([Littmann–Spanier](https://arxiv.org/abs/1311.1157)).

## The eigenvalue corollary has no polynomial-rate precedent

The nearest RH-equivalent family with a quantitative margin is Nyman–Beurling–Báez-Duarte. Here d_N is the weighted-L² distance from 1 to ζ times Dirichlet polynomials of length N.
- **Lower bounds.** Báez-Duarte, Balazard, Landreau and Saias proved lim inf d_N² log N ≥ Σ1/|ρ|² over distinct zeros on the critical line ([BCF](https://arxiv.org/abs/1211.5191)). Burnol improved the sum to Σm_ρ²/|ρ|² ([Burnol](https://arxiv.org/abs/math/0103058)). Under RH with simple zeros the constant is **2 + γ − log 4π ≈ 0.0462**.
- **Matching upper bound.** Bettin–Conrey–Farmer show the mollifier V_N attains this constant, assuming RH and Σ_{|γ|≤T}1/|ζ′(ρ)|² ≪ T^{3/2−δ} ([BCF](https://arxiv.org/abs/1211.5191)). Balazard–de Roton report that BBLS conjecture equality ([Balazard–de Roton](https://arxiv.org/abs/0812.1689)).
- **The link to Q_N.** It is the same constant as Q_N's diagonal: the (n, n) entry is n·K(1), with K(1) = Σ_ρ1/(ρ(1−ρ)) = 2 + γ − log 4π.

The proofs, however, are interpolation arguments at a fixed finite set of zeros. Kernel vectors attached to those zeros are orthogonal to the approximating space and become asymptotically orthogonal to each other as N → ∞, "exactly as in the Grenander–Rosenblatt method" ([Burnol](https://arxiv.org/abs/math/0103058)). Dimitrov and Oliveira make the interpolation structure explicit, with d²_{n,m} ∼ (1/log n)Σ_{j≤m}1/|ρ_j|² for m prescribed points ([Dimitrov–Oliveira](https://arxiv.org/abs/1608.07887)).

These are lim inf statements, ineffective in N, about the distance of one vector. They sit on the interpolation side of the Beurling–Landau dichotomy: finitely many zeros against N → ∞. The corollary sits on the sampling side: about (T/π)log T zeros against N coefficients. Neither implies the other.

Weil's quadratic form on windows behaves the opposite way. For small support it is positive. That is Yoshida's theorem, as restated by Connes–Consani ([Connes–Consani 2021](https://arxiv.org/abs/2006.13771)). Its lowest eigenvalue grows like log(1/a) as the window [−a, a] shrinks ([Suzuki 2026, preprint](https://arxiv.org/abs/2606.09096)). As the window grows, the smallest eigenvalues collapse: **Connes–Consani found 2.389 × 10⁻⁴⁸ at λ² = 11**. Those eigenvalues are carried by "prolate vectors" E(f)(x) = x^{1/2}Σf(nx), whose Mellin transforms contain ζ ([Connes–Consani 2023](https://arxiv.org/abs/2106.01715)).

An unrefereed 2026 preprint fits −ln λ_min ≈ 2π²N(T*)/ln N(T*) with T* = 2πe^{2L}, and proves λ*(L) ≤ exp(−Le^L) under RH ([Zhu, preprint](https://arxiv.org/abs/2608.24827)). The research notes checked that the two sources agree to about 4% at λ² = 11. Li's criterion is not an eigenvalue problem; under RH its coefficients grow like (n/2)log n ([Lagarias](https://arxiv.org/abs/math/0404394)). **No published or preprint result was found giving a polynomial lower bound, c/N or N^{−A}, for the smallest eigenvalue of any RH-related positive form on N-dimensional test spaces.**

The gap between exp(−cN) and c/N comes from the norm, not from the zeros; this reading is the notes' inference. On a window, the L² norm lets f̂ concentrate below T*, where the zeros are sparser than the Landau density, so Σ_γ|f̂(γ)|² can be tiny. The coefficient norm of a Dirichlet polynomial forbids that concentration, because the polynomial's mean square is equidistributed at scales ≫ N. The crossover is the same in both settings, with T* matching 2πN.

The corollary is therefore, as far as could be found, **the first polynomial positivity margin for an RH-equivalent family of Gram matrices**. The project's `BallRate.rh_iff_balance` makes "Q_N ⪰ 0 for all N" equivalent to RH, a point the literature searched never addresses. The margin is sharp up to a logarithm. Numerically, λ_N ≈ 0.048·log N/N up to N = 2000 ([ball-rate.md](../formalisations/ball-rate.md)), and the alternating vector x_n = (−1)^{n−1}/n heuristically gives λ_N ≪ (log N)²/N (the notes' heuristic).

The same Gram construction can be run with n^ρ replaced by z_ρ^k = (1 − 1/ρ)^k. It produces Toeplitz matrices of second differences of Li coefficients, λ_{m+1} − 2λ_m + λ_{m−1}, which are positive semidefinite under RH. That construction is also derived in the notes, and no study of its smallest eigenvalues was found.

## What ball-rate.md should cite, and how much was checked

The BallCutoff section currently cites no literature. The first table lists what it should carry. The second lists optional context for the "What is missing", `BallSampling` and `BallDensity` sections.

- **"Primary"** means the research read the statement in the source itself (arXiv full text, or the author's PDF where noted).
- **"Secondary"** means the statement is known only through the later papers named.
- **"Metadata"** records where the bibliographic data were checked during this write-up: Crossref, the arXiv record, or only the citing papers.

**Core citations**

| Reference | Where it belongs in ball-rate.md | Statement checked | Metadata |
|---|---|---|---|
| H. M. Bui, A. Florea, M. B. Milinovich, "Negative discrete moments of the derivative of the Riemann zeta-function", *Bull. London Math. Soc.* 56 (2024), no. 8, 2680–2703, [doi:10.1112/blms.13092](https://doi.org/10.1112/blms.13092), [arXiv:2310.03949](https://arxiv.org/abs/2310.03949) | `sampling_rh`: closest prior theorem (Thm 3.1) and the range N ≤ cT/log²T it reaches | Primary (arXiv v1; numbering in the journal version not checked) | Crossref |
| S. M. Gonek, "An explicit formula of Landau and its applications to the theory of the zeta-function", *Contemp. Math.* 143, AMS, 1993, 395–413, [doi:10.1090/conm/143/1210528](https://doi.org/10.1090/conm/143/1210528) | the uniform Landau formula (Thm 1) behind BFM | Secondary (Milinovich L. 4.1; BFM L. 3.2; DHP Cor. 2.1) | Crossref |
| S. M. Gonek, "A formula of Landau and mean values of ζ(s)", in *Topics in Analytic Number Theory* (Austin, 1982), Univ. of Texas Press, 1985, 92–97 | the first uniform version | Secondary (Milinovich; DHP) | citing papers only |
| E. Landau, "Über die Nullstellen der Zetafunktion", *Math. Ann.* 71 (1911), no. 4, 548–564, [doi:10.1007/BF01456808](https://doi.org/10.1007/BF01456808) | Landau's formula, already named in the note | Not consulted; formula via DHP and Goldston; matched to this paper by title and year | Crossref (dates the issue 1912) |
| N. Ng, "Extreme values of ζ′(ρ)", *J. London Math. Soc.* (2) 78 (2008), no. 2, 273–289, [doi:10.1112/jlms/jdn022](https://doi.org/10.1112/jlms/jdn022), [arXiv:0706.1765](https://arxiv.org/abs/0706.1765) | the asymptotic for N = T^θ, θ < 1 (Prop. 4(i)) | Primary (arXiv) | Crossref |
| H. L. Montgomery, A. M. Odlyzko, "Gaps between zeros of the zeta function", in *Topics in Classical Number Theory* (Budapest, 1981), Colloq. Math. Soc. János Bolyai 34, North-Holland, 1984, 1079–1106 | earliest explicit-formula argument with a Dirichlet-polynomial weight and the Landau form; source of the Beurling–Selberg lemma | Secondary (BMN; GTT; Goldston–Gonek) | citing papers only |
| J. B. Conrey, A. Ghosh, S. M. Gonek, "A note on gaps between zeros of the zeta function", *Bull. London Math. Soc.* 16 (1984), no. 4, 421–424, [doi:10.1112/blms/16.4.421](https://doi.org/10.1112/blms/16.4.421) | windowed sampling form M₂(c)/M₁; the AM–GM bound behind `landau_le` | Secondary (BMN; GTT) | Crossref |
| D. A. Goldston, T. S. Trudgian, C. L. Turnage-Butterbaugh, "On the Montgomery–Odlyzko method regarding gaps between zeros of the zeta-function", *J. Math. Anal. Appl.* 527 (2023), no. 2, 127548, [doi:10.1016/j.jmaa.2023.127548](https://doi.org/10.1016/j.jmaa.2023.127548), [arXiv:2201.10676](https://arxiv.org/abs/2201.10676) | modern statement of the method and its barriers | Primary (arXiv) | Crossref |
| H. Iwaniec, E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004, Thm 5.12, [doi:10.1090/coll/053](https://doi.org/10.1090/coll/053) | the explicit formula in `weil_htC` | Not checked against the book; Goldston–Gonek and CMS cite it for this | Crossref |
| D. A. Goldston, S. M. Gonek, "A note on S(t) and the zeros of the Riemann zeta-function", *Bull. London Math. Soc.* 39 (2007), no. 3, 482–486, [doi:10.1112/blms/bdm032](https://doi.org/10.1112/blms/bdm032), [arXiv:math/0511092](https://arxiv.org/abs/math/0511092) | template: explicit formula plus band-limited minorant; the mass bound ∫F⁻ ≥ 2L − 1/δ | Primary (arXiv) | Crossref |
| E. Carneiro, M. B. Milinovich, K. Soundararajan, "Fourier optimization and prime gaps", *Comment. Math. Helv.* 94 (2019), no. 3, 533–568, [doi:10.4171/CMH/467](https://doi.org/10.4171/CMH/467), [arXiv:1708.04122](https://arxiv.org/abs/1708.04122) | the one-term case f(z)a^{iz} of \|D\|²Φ | Primary (arXiv) | arXiv record |
| C. P. Hughes, Z. Rudnick, "Linear statistics for zeros of Riemann's zeta function", *C. R. Math. Acad. Sci. Paris* 335 (2002), no. 8, 667–670, [doi:10.1016/S1631-073X(02)02541-4](https://doi.org/10.1016/S1631-073X(02)02541-4), [arXiv:math/0208220](https://arxiv.org/abs/math/0208220) | the separation argument behind `sep_log` | Primary (arXiv) | Crossref |
| H. L. Montgomery, "The pair correlation of zeros of the zeta function", in *Analytic Number Theory*, Proc. Sympos. Pure Math. 24, AMS, 1973, 181–193, [doi:10.1090/pspum/024/9944](https://doi.org/10.1090/pspum/024/9944) | compact Fourier support makes sums over zeros computable | Secondary (Goldston's notes) | Crossref |
| J. D. Vaaler, "Some extremal functions in Fourier analysis", *Bull. Amer. Math. Soc. (N.S.)* 12 (1985), no. 2, 183–216, [doi:10.1090/S0273-0979-1985-15349-2](https://doi.org/10.1090/S0273-0979-1985-15349-2) | Beurling–Selberg band-limited majorants and minorants | Not read | Crossref (settles the page range 183–216) |
| H. L. Montgomery, "The analytic principle of the large sieve", *Bull. Amer. Math. Soc.* 84 (1978), no. 4, 547–567, [doi:10.1090/S0002-9904-1978-14497-8](https://doi.org/10.1090/S0002-9904-1978-14497-8) | Selberg's band-limited large sieve, the tradition of the Fejér-majorant bound `integral_Kc_majR_le` | Not read | Crossref |
| H. L. Montgomery, R. C. Vaughan, "Hilbert's inequality", *J. London Math. Soc.* (2) 8 (1974), no. 1, 73–82, [doi:10.1112/jlms/s2-8.1.73](https://doi.org/10.1112/jlms/s2-8.1.73) | the mean-value theorem T + O(n) (Cor. 3), invoked without citation in `BallSampling` | Secondary (BFM; Milinovich–Ng 2012) | Crossref |
| E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Thm 4.11 (the note already cites the book) | necessity of T ≳ 2πN | Secondary (search summary of arXiv:1203.2242; Arias de Reyna) | edition not checked |
| J. Arias de Reyna, "On the approximation of the zeta function by Dirichlet polynomials", [arXiv:2406.16667](https://arxiv.org/abs/2406.16667) (2024) | explicit Thm 4.11: rigorous failure at T = N | Primary (abstract) | arXiv record; no journal version found |
| H. J. Landau, "Necessary density conditions for sampling and interpolation of certain entire functions", *Acta Math.* 117 (1967), 37–52, [doi:10.1007/BF02395039](https://doi.org/10.1007/BF02395039) | the Nyquist / Beurling–Landau comparison already made in the note | Secondary (Olevskii–Ulanovskii; Ortega-Cerdà–Seip); PDF located, not read | Crossref |
| J. Ortega-Cerdà, K. Seip, "Fourier frames", *Ann. of Math.* (2) 155 (2002), no. 3, 789–806, [arXiv:math/0005092](https://arxiv.org/abs/math/0005092) | the critical-density case: why density alone decides nothing at θ = 0 | Primary (arXiv) | arXiv record |
| L. Báez-Duarte, M. Balazard, B. Landreau, E. Saias, "Notes sur la fonction ζ de Riemann, 3", *Adv. Math.* 149 (2000), no. 1, 130–144, [doi:10.1006/aima.1999.1861](https://doi.org/10.1006/aima.1999.1861) | `rate_cut`: the Nyman–Beurling lower bound with the same constant H₀ | Secondary (Burnol; BCF) | Crossref |
| J.-F. Burnol, "A lower bound in an approximation problem involving the zeros of the Riemann zeta function", *Adv. Math.* 170 (2002), no. 1, 56–70, [doi:10.1006/aima.2001.2066](https://doi.org/10.1006/aima.2001.2066), [arXiv:math/0103058](https://arxiv.org/abs/math/0103058) | same, with m_ρ²; the interpolation mechanism | Primary (arXiv) | Crossref |
| A. Connes, C. Consani, "Spectral triples and ζ-cycles", *Enseign. Math.* 69 (2023), 93–148, [doi:10.4171/LEM/1049](https://doi.org/10.4171/LEM/1049), [arXiv:2106.01715](https://arxiv.org/abs/2106.01715) | `rate_cut`: contrast with super-exponentially small eigenvalues on windows | Primary (arXiv) | Crossref |

**Optional context citations**

| Reference | Use | Statement checked | Metadata |
|---|---|---|---|
| M. B. Milinovich, N. Ng, "A note on a conjecture of Gonek", *Funct. Approx. Comment. Math.* 46 (2012), no. 2, 177–187, [doi:10.7169/facm/2012.46.2.3](https://doi.org/10.7169/facm/2012.46.2.3) | Möbius case for every ϑ < 1; survey of methods | Primary (author's PDF) | Crossref |
| M. B. Milinovich, "Upper bounds for the moments of ζ′(ρ)", *Bull. London Math. Soc.* 42 (2010), no. 1, 28–44, [doi:10.1112/blms/bdp096](https://doi.org/10.1112/blms/bdp096), [arXiv:0806.0786](https://arxiv.org/abs/0806.0786) | upper bound up to length T/log T | Primary (arXiv) | arXiv record |
| S. Kirila, "An upper bound for discrete moments of the derivative of the Riemann zeta-function", *Mathematika* 66 (2020), 475–497, [doi:10.1112/mtk.12008](https://doi.org/10.1112/mtk.12008), [arXiv:1804.08826](https://arxiv.org/abs/1804.08826) | the Landau term is "not positive" and of the diagonal's order | Primary (arXiv) | arXiv record |
| B. Durkan, C. Hughes, A. Pearce-Crump, "Generalisations of the Landau–Gonek theorem and applications to mean values of zeta", [arXiv:2601.18025](https://arxiv.org/abs/2601.18025) (2026) | Landau–Gonek errors dominate at length ≍ height | Primary (arXiv); unrefereed preprint | arXiv record |
| H. M. Bui, M. B. Milinovich, N. Ng, "A note on the gaps between consecutive zeros of the Riemann zeta-function", *Proc. Amer. Math. Soc.* 138 (2010), no. 12, 4167–4175, [doi:10.1090/S0002-9939-2010-10443-4](https://doi.org/10.1090/S0002-9939-2010-10443-4), [arXiv:0910.2052](https://arxiv.org/abs/0910.2052) | exposition of Montgomery–Odlyzko / CGG and the barriers 1/2 and 6.2 | Primary (arXiv) | Crossref |
| E. Carneiro, V. Chandee, F. Littmann, M. B. Milinovich, "Hilbert spaces and the pair correlation of zeros of the Riemann zeta-function", *J. reine angew. Math.* 725 (2017), 143–182, [doi:10.1515/crelle-2014-0078](https://doi.org/10.1515/crelle-2014-0078), [arXiv:1406.5462](https://arxiv.org/abs/1406.5462) | reproducing-kernel optimisation; a measure vanishing at 0 | Primary (abstract and introduction) | arXiv record |
| F. Littmann, M. Spanier, "Extremal functions with vanishing condition", *Constr. Approx.* 42 (2015), no. 2, 209–229, [doi:10.1007/s00365-015-9304-4](https://doi.org/10.1007/s00365-015-9304-4), [arXiv:1311.1157](https://arxiv.org/abs/1311.1157) | nearest extremal minorant with a prescribed zero | Primary (abstract) | Crossref |
| D. A. Goldston, "Notes on pair correlation of zeros and prime numbers", [arXiv:math/0412313](https://arxiv.org/abs/math/0412313) | Selberg's minorant and the Fejér pair | Primary (arXiv) | arXiv record; published version not checked |
| H. L. Montgomery, *Ten Lectures on the Interface between Analytic Number Theory and Harmonic Analysis*, CBMS Regional Conf. Ser. Math. 84, AMS, 1994, §7.2 Thm 1, [doi:10.1090/cbms/084](https://doi.org/10.1090/cbms/084) | continuous two-sided (T ± 2πN)‖a‖² | Secondary (Harrison's Warwick notes) | Crossref |
| A. E. Ingham, "Some trigonometrical inequalities with applications to the theory of series", *Math. Z.* 41 (1936), 367–379, [doi:10.1007/BF01180426](https://doi.org/10.1007/BF01180426) | inverse inequality beyond 2π/(frequency gap) | Secondary (Jaming–Komornik) | Crossref |
| A. Beurling, *The Collected Works of Arne Beurling*, vol. 2, Birkhäuser, 1989 ("Balayage of Fourier–Stieltjes transforms"; "Interpolation for an interval in ℝ") | sampling iff the lower uniform density exceeds σ/π | Secondary (Olevskii–Ulanovskii) | citing papers only |
| A. Olevskii, A. Ulanovskii, "On the duality between sampling and interpolation", *Anal. Math.* 42 (2016), no. 1, 43–53, [doi:10.1007/s10476-016-0104-2](https://doi.org/10.1007/s10476-016-0104-2), [arXiv:1512.01437](https://arxiv.org/abs/1512.01437) | statements of Beurling's, Landau's and Kahane's theorems | Primary (arXiv) | Crossref |
| H. M. Bui, M. B. Milinovich, "Gaps between zeros of the Riemann zeta-function", *Q. J. Math.* 69 (2018), no. 2, 403–423, [doi:10.1093/qmath/hax047](https://doi.org/10.1093/qmath/hax047), [arXiv:1410.3635](https://arxiv.org/abs/1410.3635) | gaps beyond 3.18 mean spacings: why maximal-gap methods fail | Primary (arXiv) | Crossref |
| J.-F. Olsen, E. Saksman, "On the boundary behaviour of the Hardy spaces of Dirichlet series and a frame bound estimate", *J. reine angew. Math.* 663 (2012), 33–66, [doi:10.1515/crelle.2011.093](https://doi.org/10.1515/crelle.2011.093), [arXiv:0907.2708](https://arxiv.org/abs/0907.2708) | the dual frame problem at ±log n | Primary (arXiv) | Crossref; pages from Saksman–Seip |
| S. Bettin, J. B. Conrey, D. W. Farmer, "An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion", *Proc. Steklov Inst. Math.* 280 (2013), suppl. 2, 30–36 (Russian original: Sovrem. Probl. Mat. 16 (2012), 38–44), [doi:10.1134/S0081543813030036](https://doi.org/10.1134/S0081543813030036), [arXiv:1211.5191](https://arxiv.org/abs/1211.5191) | conditional d_N² ∼ H₀/log N | Primary (arXiv) | arXiv record |
| A. Connes, C. Consani, "Weil positivity and trace formula, the archimedean place", *Selecta Math. (N.S.)* 27 (2021), no. 4, [doi:10.1007/s00029-021-00689-4](https://doi.org/10.1007/s00029-021-00689-4), [arXiv:2006.13771](https://arxiv.org/abs/2006.13771) | small-support Weil positivity (Yoshida) | Primary (arXiv) | Crossref |
| H. Yoshida, "On Hermitian forms attached to zeta functions", in *Zeta Functions in Geometry*, Adv. Stud. Pure Math. 21 (1992), 281–325, [Project Euclid](https://projecteuclid.org/ebooks/advanced-studies-in-pure-mathematics/Zeta-Functions-in-Geometry/chapter/On-Hermitian-Forms-attached-to-Zeta-Functions/10.2969/aspm/02110281.pdf) | same | Secondary (Connes–Consani; Suzuki) | Project Euclid URL only |
| H. Davenport, *Multiplicative Number Theory*, Graduate Texts in Math., Springer, 2nd ed. 1980, ch. 12, [doi:10.1007/978-1-4757-5927-3](https://doi.org/10.1007/978-1-4757-5927-3) | H₀ = Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π | Secondary (Balazard–de Roton cite it for this) | Crossref |
| X.-J. Li, "The positivity of a sequence of numbers and the Riemann hypothesis", *J. Number Theory* 65 (1997), no. 2, 325–333, [doi:10.1006/jnth.1997.2137](https://doi.org/10.1006/jnth.1997.2137) | another RH-equivalent positivity family | Secondary (Lagarias) | Crossref |

Five passages in the note should change in light of the literature.

1. **The density phrasing.** The closing paragraph of the BallCutoff section calls the theorem "the Marcinkiewicz–Zygmund inequality at a constant multiple of the Nyquist density". At T = CN the density exceeds Nyquist only by (1/2π)log(C/2π), so it should read "at the Nyquist density plus an additive constant", or "at heights a constant multiple of the crossover 2πN". The "What is missing" section already says this correctly.
2. **Superseded routes.** Statement 3B and "What is missing" say the inequality would follow from Landau's formula with a pair-correlation input, and that Beurling–Landau "needs θ > 0". BallCutoff uses neither Landau–Gonek nor pair correlation, and the Landau–Gonek route stalls at T ≍ N (BFM's error term; DHP). The θ > 0 remark is accurate only as a statement about Beurling's sufficient condition, and should cite Beurling and Ortega-Cerdà–Seip.
3. **The novelty claim.** It should be "the first lower bound in the linear range T ≍ N, pointwise, with explicit constants", not "the first lower bound". BFM plus CGG's AM–GM bound give a stronger but inexplicit one for N ≤ cT/log²T, and Montgomery–Odlyzko/CGG give a windowed one.
4. **Attributions in the proof.**
   - `landau_le` should credit CGG's AM–GM device.
   - `sep_log` should cite Hughes–Rudnick.
   - `weil_htC` should cite Iwaniec–Kowalski Thm 5.12.
   - The Fejér-majorant bound should cite the Selberg–Montgomery–Vaaler tradition.
5. **A sharpness sentence.** One belongs next to `sampling_rh`: the inequality fails for T ≤ (2π − ε)N, so only the constant e²⁴ is at stake.

### What could not be verified

The statements the note leans on most are known here only second-hand.

**Gonek's papers.** Gonek's 1985 and 1993 papers were not accessed. Their uniform formula is reproduced identically by five later papers, so the statement is reliable. Whether Gonek 1993 itself proves a Σ|A(ρ)|² theorem was not checked.

**Landau's 1911 paper.** It was not consulted, and its bibliographic match is by title and year only.

**Montgomery–Odlyzko 1984.** How the explicit formula is arranged there, whether as |A|²F(t − τ) integrated in τ or otherwise, is unknown.

**Conrey–Ghosh–Gonek.** The "c ≥ 6.2" barrier, and its uniformity over all coefficients, rest on BMN's and GTT's summaries.

**Taken from later quotations:**
- Montgomery–Vaughan's Corollary 3;
- Montgomery's *Ten Lectures* §7.2;
- Ingham's constants;
- Iwaniec–Kowalski's Theorems 5.12 and 9.4;
- Titchmarsh's Theorem 4.11 (seen only in a search summary);
- Vaaler 1985;
- Montgomery 1973 and 1978;
- Rudnick–Sarnak 1996;
- BBLS 2000;
- Yoshida 1992;
- Bombieri 2000/2003;
- Beurling's collected works;
- H. J. Landau 1967.

**Not checked at all:**
- Ford–Zaharescu's Lemma 1 as quoted by Radziwiłł;
- Theorem 1.3 of Ng's preprint on discrete mean values;
- Montgomery's *Topics in Multiplicative Number Theory* (LNM 227) on the large sieve at zeros;
- the "(T + N)log T" upper bounds attributed to Ramachandra and Jutila.

**Search coverage.** MathSciNet and zbMATH could not be queried. The searches covered arXiv metadata, general web search and selected full texts, so the absence of the theorem from the literature is established only to that extent.

**Open questions with no source.** Three questions found no answer anywhere:
- whether Σ ≫ T log(T/N)‖b‖² uniformly for T ≥ CN is known (presumably it is open);
- where in [2πN, e²⁴N] the optimal threshold lies;
- whether the smallest eigenvalues of Nyman–Beurling Gram matrices have been studied (Landreau–Richard's 2002 numerics were not read).

**Preprints.** DHP 2026, Zhu 2026 and Suzuki 2026 are unrefereed, and Zhu's decay law is fitted, not derived.

**Metadata.** The bibliographic data in the tables were checked against Crossref or arXiv records during this write-up, with these exceptions:
- Gonek 1985, Montgomery–Odlyzko 1984 and Beurling 1989: data from citing papers only;
- Yoshida 1992: from its Project Euclid URL only;
- Titchmarsh: edition not checked.

## Conclusion

The literature reaches the zeros from two sides and stops short of the middle. Landau–Gonek mean values are exact in the coefficients, but their near-miss errors swamp the main term at T ≍ N. Montgomery–Odlyzko smoothing removes those errors, but at the cost of windows and length T/log²T. BallCutoff gets both properties at once by making the Fourier support smaller than the arithmetic separation. That turns an asymptotic into an identity and moves every loss into the archimedean term and the shape of Φ.

The relocation is the useful lesson. The guaranteed sampling mass is, to leading order, the integrated surplus of zeros over the Nyquist count, and the 143-fold gap to the heuristic constant is exactly the mass Φ gives up. So the natural next theorem, Σ ≫ T·log(T/N)·‖b‖² from a threshold near 2πN, is a one-dimensional extremal problem for band-limited minorants with a vanishing condition, not a question needing new arithmetic input.

For the corollary, the comparison with Nyman–Beurling and with Weil windows shows that conditioning in RH-equivalent positivity criteria is decided by the norm on the test space. Under RH, coefficient-normed Dirichlet polynomials get a polynomial margin c/N, while L²-normed windows get exp(−cN). Criteria built on Dirichlet-polynomial test spaces, such as Q_N, are therefore the ones whose positivity can be certified at finite N. The note should present `sampling_rh` as the first sampling inequality at the zeros in the linear range, with explicit constants, and `rate_cut` as the first polynomial margin for such a criterion. It should not claim the first lower bound for discrete mean values, since Bui–Florea–Milinovich's theorem already implies one in a shorter range.
