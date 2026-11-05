# Discrete mean values of Dirichlet polynomials over the zeros of ζ, and lower ("sampling") bounds

Scope: what is known about Σ_{0<γ≤T} |A(ρ)|² for A(s) = Σ_{n≤N} a(n) n^{-s}: main terms, error terms, admissible N versus T, RH assumptions, and whether anything gives a uniform lower bound ≥ c·T·Σ|a(n)|²/n when T ≍ N. The result being checked (RH, Lean) is: for T ≥ e^24·N, Σ_{|γ|≤T} |Σ_{n≤N} b_n n^{iγ}|² ≥ (T/100)·Σ b_n².

Notation used throughout these notes (a derived dictionary, not a cited fact). Under RH, conj(ρ) = 1 − ρ and |n^{-ρ}| = n^{-1/2}. The user's Σ x_n n^ρ with real x_n corresponds to a(n) = n·x_n and b_n = x_n·√n = a(n)/√n. Then Σ|a(n)|²/n = Σ x_n² n = Σ b_n². The Landau cross term a(m)·conj(a(mk))·Λ(k)/(mk) becomes b_m·conj(b_{mk})·Λ(k)/√k. For real coefficients, Σ_{|γ|≤T} = 2·Σ_{0<γ≤T}. So the user's bound is equivalent to Σ_{0<γ≤T} |Σ b_n n^{-iγ}|² ≥ (T/200)·Σ b_n².

## 1. Gonek's uniform Landau formula: exact statement, and the discrete mean value it gives

### Takeaway
Gonek's uniform Landau formula holds without RH and with explicit error terms. It is attributed to Gonek's papers of 1985 (Austin proceedings) and 1993 (Contemp. Math. 143, Theorem 1). Combined with RH, it gives the cleanest general statement, Bui–Florea–Milinovich (2023), Theorem 3.1:

Σ_{0<γ≤T} |Σ_{n≤x} a_n n^{-ρ}|² = N(T)·Σ|a_n|²/n − (T/π)·Re Σ_{kn≤x} a_{kn}·conj(a_n)·Λ(k)/(kn) + O(x·log²(xT)·Σ|a_n|²/n),

for all x ≥ 2 and T > 1. The error term is larger than the diagonal unless x = o(T/log T), so at T ≍ N the formula carries no information.

### Cited Findings
- **Gonek's uniform formula, unconditional.** For x, T > 1:
  Σ_{0<γ≤T} x^ρ = −(T/2π)·Λ(x) + O(x·log(2xT)·log log(3x)) + O(log x·min(T, x/⟨x⟩)) + O(log(2T)·min(T, 1/log x)).
  Here ⟨x⟩ is the distance from x to the nearest prime power other than x itself. Λ(x) = log p if x is a positive integral power of a prime p, and Λ(x) = 0 otherwise. Milinovich states this as Lemma 4.1, "due to Gonek [6, 8]". Ref. [6] is Gonek, "A formula of Landau and mean values of ζ(s)", Topics in Analytic Number Theory (Austin), Univ. Texas Press 1985, 92–97. Ref. [8] is Gonek, "An explicit formula of Landau and its applications to the theory of the zeta function", Contemp. Math. 143 (1993), 395–413. — [Milinovich, arXiv:0806.0786 (Bull. LMS 42 (2010) 28–44)](https://arxiv.org/abs/0806.0786)
- The same statement appears as Lemma 3 of Milinovich–Ng. — [Milinovich–Ng, arXiv:0706.2321](https://arxiv.org/abs/0706.2321)
- Bui–Florea–Milinovich quote the identical statement as their Lemma 3.2, citing it as "[9, Theorem 1]", where [9] is Gonek, Contemp. Math. 143 (1993). — [Bui–Florea–Milinovich, arXiv:2310.03949](https://arxiv.org/abs/2310.03949)
- Durkan–Hughes–Pearce-Crump give:
  - **Landau's original theorem (1911):** for fixed X > 1, Σ X^ρ = −(T/2π)Λ(X) + O(log T).
  - **Gonek's formula**, labelled "Theorem 2 (Gonek, 1985)". They add: "When we restrict X to be an integer, Gonek also notes that the last two error terms are subsumed by the first two error terms. He also highlights the highly different behaviour between the case when X is an integer and when X is an arbitrary real number."
  - **The reflected version, "Corollary 2.1 (Gonek, 1993)":**
    Σ_{0<γ≤T} X^{-ρ} = −T·Λ(X)/(2πX) + O(log(2XT)·log log(3X)) + O(log X·min(T/X, 1/⟨X⟩)) + O(log(2T)·min(T/X, 1/(X log X))).
  - **Fujii's extension:** "Gonek's result was further generalised by Fujii [Proc. Japan Acad. 65 (1989) 51–54; 66 (1990) 291–296] who found lower order terms in the expansion."

  — [Durkan–Hughes–Pearce-Crump, arXiv:2601.18025 (2026)](https://arxiv.org/abs/2601.18025)
- **RH-normalised form (Çiçek).** Assume RH, x > 1, T ≥ 2. Then Σ_{0<γ≤T} x^{iγ} = −(T/2π)·Λ(x)/√x + E(x,T), with
  E ≪ √x·log(xT)·log log(3x) + (log x/√x)·min(T, x/⟨x⟩) + (log T/√x)·min(T, 1/log x).
  Çiçek writes: "Landau proved a weaker version … the error term was not uniform in x. The above version was later proven by Gonek [1985, 1993]." — [Çiçek, arXiv:2007.10533](https://arxiv.org/abs/2007.10533)
- **Integer-ratio form (Kirila, Lemma 5.1).** Assume RH, and let a > b be positive integers. Then Σ_{T<γ≤2T} (a/b)^{iγ} = −(T/2π)·Λ(a/b)/√(a/b) + O(√(ab)·(log T)²). Kirila says this is "essentially the one found in" Radziwiłł (Adv. Math. 257 (2014)). — [Kirila, arXiv:1804.08826](https://arxiv.org/abs/1804.08826)
- **Near-prime-power transition (Radziwiłł, Lemma 8, "Gonek [10]").**
  - If x = a/b ≠ 1 with a, b ≤ N, then Σ_{T≤γ≤2T} x^{iγ} ≪ N·log² T.
  - The proof quotes a refinement "as noted by Ford and Zaharescu (Lemma 1)":
    Σ_{T≤γ≤2T} x^{1/2+iγ} = −(Λ(n_x)/2π)·(e^{iT log(x/n_x)} − 1)/(i·log(x/n_x)) + O(x·log²(2xT) + log 2T/log x),
    where n_x is attached to x (n_x ≠ x for non-integer x).
  - For non-integer x = a/b, Radziwiłł notes |log(x/n_x)| ≫ a^{-1} ≫ N^{-1}.

  This main term interpolates smoothly between T·Λ and 1/|log(x/n_x)| when x is close to a prime power. — [Radziwiłł, arXiv:1301.3232](https://arxiv.org/abs/1301.3232)
- **Aryan's extension.** Aryan proves "an extension of the Landau–Gonek formula" that recovers unconditionally some pair-correlation consequences previously known only under RH. One corollary is that at least two-thirds of zeros are simple under a zero-density hypothesis weaker than RH. Aryan quotes the integer case: Σ x^ρ = −(T/2π)Λ(x) + O(x·log 2xT·log log 3x). — [Aryan, arXiv:1902.05473](https://arxiv.org/abs/1902.05473)
- **The mean-value theorem it gives (Bui–Florea–Milinovich, Theorem 3.1).** "Assume RH. Then for x ≥ 2 and T > 1, we have
  Σ_{0<γ≤T} |Σ_{n≤x} a_n/n^ρ|² = N(T)·Σ_{n≤x} |a_n|²/n − (T/π)·Re Σ_{kn≤x} a_{kn}·ā_n·Λ(k)/(kn) + O(x·(log(xT))²·Σ_{n≤x} |a_n|²/n),
  where {a_n} is any sequence of complex numbers."
  - The conjugation bar was lost in PDF extraction. Its placement does not matter inside Re.
  - The authors call the theorem "of independent interest" and "similar in flavor to the Montgomery–Vaughan mean-value theorem for continuous averages [Montgomery–Vaughan, J. LMS 8 (1974), Corollary 3]".
  - The proof expands with 1 − ρ = conj(ρ) and applies Gonek 1993, Theorem 1 to each ratio (m/n)^ρ.

  — [Bui–Florea–Milinovich, arXiv:2310.03949](https://arxiv.org/abs/2310.03949)
- **Bilinear shifted version (Çiçek, Lemma 3.1).** "Assume RH … suppose that M, N ≤ T." For Σ_{0<γ≤T} (Σ_{n≤N} a_n n^{-i(γ+v)})·conj(Σ_{m≤M} b_m m^{-i(γ+v)}):
  - **Main term:** N(T)·Σ_{n≤min(M,N)} a_n·b̄_n − (T/2π)·Σ_{m≤M, n≤N} a_n·b̄_m·(m/n)^{iv}·[Λ(m/n)/√(m/n) + Λ(n/m)/√(n/m)].
  - **Errors:** O(max{M,N}·log² T·(Σ|a_n|² + Σ|b_m|²)), plus
    O(max{M,N}·log T·log log T·(Σ_m (|b_m|/√m)·Σ_{m<n≤N} |a_n|√n + Σ_n (|a_n|/√n)·Σ_{n<m≤M} |b_m|√m)).
  - **Diagonal case a = b:** N(T)·Σ|a_n|² − (T/π)·Re Σ_{m,n≤N} a_n·ā_m·(m/n)^{iv}·Λ(m/n)/√(m/n) + O(N·log T·log log T·Σ_{n<m≤N} |a_n a_m|·√(m/n)) + O(N·log² T·Σ|a_n|²).
  - The proof bounds the ⟨m/n⟩-term using ⟨m/n⟩ ≥ 1/n, giving "N times our bound for the first".
  - The lemma is used for prime polynomials of length Y ≤ (T/log T)^{1/(3k)} (Çiçek's Lemma 3.2).

  — [Çiçek, arXiv:2007.10533](https://arxiv.org/abs/2007.10533)
- Çiçek: "A formula of Landau and Gonek allows one to estimate sums of the type Σ_{0<γ≤T} A(ρ)^j·B(1−ρ)^k … provided that RH is true." — [Çiçek](https://arxiv.org/abs/2007.10533)
- Milinovich–Ng (2012), surveying [BMN 2010; CGG 1984; CGGGH 1985; Gonek 1993; Milinovich 2010; Montgomery 1973; Ng 2004; Soundararajan 1996]: "In each of these articles, the evaluation of the discrete mean (2.6) [Σ_{0<γ<T} |A(ρ)|², A of length ξ ≤ T] either makes use of the Guinand–Weil explicit formula or of Gonek's uniform version of Landau's formula." — [Milinovich–Ng, Funct. Approx. 46.2 (2012) 177–187](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)
- Gonek's Invent. Math. 75 (1984) paper is cited in this literature for the discrete second moment of ζ'. Under RH, J_1(T) = N(T)^{-1}·Σ_{0<γ≤T} |ζ'(ρ)|² ~ (1/12)(log T)³. — [Milinovich, arXiv:0806.0786](https://arxiv.org/abs/0806.0786)

### Inferences
- **Where the loss comes from.** Write x = m/n with n < m ≤ N.
  - The x·log(2xT) term contributes a bilinear form Σ_{n<m} |b_n b_m|·√(m/n)·log(NT)·log log N. The kernel √(m/n)·1_{n<m≤N} has operator norm ≍ N up to √log N. (A test vector with mass at n = 1 plus a flat tail gives ≳ N/3.)
  - The ⟨x⟩-term is largest for "near misses" m = n·p^k + j with small j. There ⟨m/n⟩ ≍ |j|/n, and the term is ≍ √(mn)·log N/|j|, which is bounded crudely in Çiçek.
  - With absolute values inside, the sharp-cutoff Landau–Gonek route therefore loses at least a factor N·polylog against the diagonal. Bui–Florea–Milinovich package the loss as O(x·log²(xT)·Σ|a|²/n).
- **At x = N = T/C.** The BFM error is ≍ (T/C)·log² T·Σb², while the diagonal N(T)·Σb² is ≍ (T/2π)·log T·Σb². The error exceeds the diagonal by a factor ≍ log T/C, so Theorem 3.1 says nothing anywhere in the range T ∈ [CN, N log N].
- **Validity ranges.** Theorem 3.1 gives an honest asymptotic when N = o(T/log T) and the diagonal is not cancelled. In the worst case the main term is only ≍ T·log(T/N)·Σb² (see Section 6), and then N ≤ T/(log T)^{2+ε} is needed.
- **Near misses matter at T ≍ N.** The Ford–Zaharescu form shows why. For pairs with |log(m/(n·p^k))| ≲ 1/T, the "near-miss" term is as large as the exact Landau term T·Λ(p^k)/√(p^k). When T ≍ N such pairs exist for every n, so they cannot be dropped and must be handled with oscillation or smoothing in T. This matches the "separation of near misses" step in the user's Lean development, as described in the task.

### Gaps
- I could not access Gonek 1985 (Austin) or Gonek 1993 (Contemp. Math. 143) directly. The formula is reproduced identically by five later papers (Milinovich; Milinovich–Ng; Bui–Florea–Milinovich; Durkan–Hughes–Pearce-Crump; Bui 0903.4007, Lemma 4.6 with T ≤ γ ≤ 2T), so the statement is reliable. I did not verify which "applications" Gonek 1993 contains, in particular whether it states its own Σ_γ |A(ρ)|² theorem. A search snippet (UTC honours thesis) says Gonek used the formula to reprove a result of Montgomery; this is unverified.
- I could not confirm whether Gonek, Invent. Math. 75 (1984) itself contains a version of the uniform x^ρ lemma. Later papers attribute the uniform lemma to the 1985 and 1993 papers.
- I did not examine the Fujii 1989/1990 papers (lower-order terms), Fujii 1995 (Comment. Math. Univ. St. Paul. 44, 59–67) or Hughes 2003 (J. Phys. A 36). They are cited only as references in the papers above.
- I did not read the original Ford–Zaharescu Lemma 1 or its journal reference, and the precise definition of n_x in it. It is used here as quoted by Radziwiłł.

## 2. Conrey–Ghosh–Gonek and the gaps-between-zeros (Montgomery–Odlyzko) method

### Takeaway
In the gaps literature, discrete means over zeros are taken at lengths K = T(log T)^{-2} (Montgomery–Odlyzko, Bui–Milinovich–Ng, Feng–Wu) or T^{1−ε} (Conrey–Ghosh–Gonek 1984). They are always integrated over a shift window |α| ≤ πc/log T and use special coefficient families. Methods involving ζ(s)×(polynomial) need GRH and lengths T^{1/2−ε}. The Landau term enters explicitly as the subtracted quadratic form in h(c). These papers deliberately choose ζ-like coefficients so that A is small at the zeros, which is exactly the cancellation of the diagonal. According to BMN, Conrey–Ghosh–Gonek (1984) show the ratio h(c) exceeds 1 whenever c ≥ 6.2, which BMN present as a limit of the method; I did not check this in the primary paper. That is the closest thing in this literature to a uniform "sampling" lower bound, but it holds only for the α-averaged sum.

### Cited Findings
- **The Montgomery–Odlyzko set-up (BMN's exposition).** Assume RH and put K = T(log T)^{-2}. Define
  h(c) = c − Re(Σ_{nk≤K} a_k·a_{nk}·g_c(n)·Λ(n)·n^{-1/2}) / Σ_{k≤K} |a_k|², with g_c(n) = 2·sin(πc·log n/log T)/(π·log n).
  "By an argument using the Guinand–Weil explicit formula … Montgomery & Odlyzko show that if h(c) < 1 for some choice of c > 0 and a sequence {a_n} then λ ≥ c and that if h(c) > 1 … then µ ≤ c." — [Bui–Milinovich–Ng, arXiv:0910.2052 (Proc. AMS 138 (2010) 4167–4175)](https://arxiv.org/abs/0910.2052)
- **The CGG reformulation.** Conrey–Ghosh–Gonek give "an alternative, and much simpler, way" in terms of A(t) = Σ_{k≤K} a_k k^{-it}:
  M_1 = ∫_T^{2T} |A(t)|² dt and M_2(c) = ∫_{−πc/log T}^{πc/log T} Σ_{T≤γ≤2T} |A(γ+α)|² dα.
  Then M_2(µ) ≤ M_1 ≤ M_2(λ), and "using standard techniques … M_2(c)/M_1 = h(c) + o(1)". BMN add: "we should choose a test function A(t) which is small near the zeros of ζ(s) to exhibit large gaps." — [BMN](https://arxiv.org/abs/0910.2052)
- **Coefficient choices and results.**
  - Montgomery–Odlyzko: a_k = k^{-1/2}·f(log k/log K), and a Liouville-twisted version. Results: λ > 1.9799 and µ < 0.5179.
  - CGG (Bull. LMS 16 (1984) 421–424): a_k = d_r(k)/√k and λ(k)·d_r(k)/√k. r = 2.2 gives λ > 2.337; r = 1.1 gives µ < 0.5172.
  - BMN: d_r(k)·k^{-1/2}·f(log(K/k)/log K), "approximates ζ(1/2+it)^r". Results under RH: λ > 2.69, µ < 0.5155.

  — [BMN](https://arxiv.org/abs/0910.2052); MO numbers and K = T(log T)^{-2} also in [Feng–Wu, arXiv:1003.0752](https://arxiv.org/abs/1003.0752)
- **Limits of the method.** "It is known that this is not attainable using Montgomery and Odlyzko's method. Specifically, in [CGG 1984], it is shown that h(c) < 1 if c < 1/2 and h(c) > 1 if c ≥ 6.2." — [BMN, §5](https://arxiv.org/abs/0910.2052)
- Bui gives the CGG 1984 polynomial as H(s) = Σ_{n≤T^{1−ε}} d_{2.2}(n)·n^{-s}, giving λ > 2.337. — [Bui, arXiv:0903.4007](https://arxiv.org/abs/0903.4007)
- **Methods with a ζ factor need GRH.**
  - CGG, Mathematika 33 (1986) 212–238, assuming GRH: H(s) = ζ(s)·Σ_{n≤T^{1/2−ε}} n^{-s} gives λ > 2.68.
  - Ng: ζ(s)·Σ_{n≤y} d_r(n)·P[n]·n^{-s} with y = T^{1/2−ε} gives λ > 3.
  - "In the last two papers, the assumption of GRH is necessary in order to estimate the discrete mean value over the zeros in M_2(H,T;c)."
  - Bui himself uses H = H_1 + ζ·H_2, lemmas with y = T^ϑ, 0 < ϑ < 1/2, and gets λ > 3.033 on GRH.

  — [Bui, arXiv:0903.4007](https://arxiv.org/abs/0903.4007)
- **Feng–Wu.** Under RH, with K = T(log T)^{-2}, infinitely often consecutive zeros differ by at least 2.7327 times the average spacing. — [Feng–Wu, arXiv:1003.0752](https://arxiv.org/abs/1003.0752)
- **Hall.** Bui records Hall's λ > 2.6306 (Mathematika 52 (2005)) and notes: "The results in Hall's paper are actually unconditional, but a lower bound for λ can only be obtained if the Riemann Hypothesis is assumed." Mueller's earlier λ ≥ 1.9 is "an immediate consequence of a mean value theorem of Gonek" (Feng–Wu). — [Bui](https://arxiv.org/abs/0903.4007); [Feng–Wu](https://arxiv.org/abs/1003.0752)
- **CGG 1998 (Simple zeros, Proc. LMS 76) via Bui–Heath-Brown.**
  - The object is mollified moments of ζ', not Σ|B(ρ)|², with mollifier B(s) = Σ_{k≤y} μ(k)·P(log(y/k)/log y)·k^{-s}, y = T^ϑ, 0 < ϑ < 1/2.
  - CGG assumed RH + GLH and obtained κ* ≥ 19/27 and κ_d ≥ 0.84568.
  - Bui–Heath-Brown remove GLH using Heath-Brown's generalisation of Vaughan's identity. On RH alone they get κ* ≥ 19/27 and κ_d ≥ 0.84665.
  - Their Lemma 1 (S_1 = Σ_{0<γ≤T} Bζ'(ρ)) carries an error O_ε(y·T^{1/2+ε}), which is what forces ϑ < 1/2.

  — [Bui–Heath-Brown, arXiv:1302.5018](https://arxiv.org/abs/1302.5018)

### Inferences
- **The pure discrete sum at the zeros.** Formally, M_2(c) ≈ (2πc/log T)·Σ_γ |A(γ)|² as c → 0, and g_c(n) ≈ 2c/log T. So the MO/CGG expansion gives
  Σ_{T≤γ≤2T} |A(γ)|² ≈ (T·log T/2π)·[Σ|a_k|² − (2/log T)·Re Σ a_k a_{nk} Λ(n) n^{-1/2}],
  i.e. the diagonal minus the Landau term. This is the same structure as BFM's Theorem 3.1.
- **Cancellation with ζ-like coefficients.** For a_k = k^{-1/2} and K = T^{1−o(1)}, the bracket is ≈ log K·(1 − log K/log T). The literature's ζ-like test polynomials are exactly those for which the Landau term nearly cancels the diagonal.
- **c ≥ 6.2 as a smoothed sampling bound.** CGG's "h(c) > 1 for c ≥ 6.2" (as reported by BMN) says: for every A of length ≤ T(log T)^{-2},
  ∫_{|α|≤πc/log T} Σ_{T≤γ≤2T} |A(γ+α)|² dα ≥ (1+o(1))·∫_T^{2T} |A|²,
  with windows of about ±3.1 mean spacings. This is a uniform-in-coefficients sampling-type lower bound, but only for zeros smeared over a window, and only at lengths ≤ T(log T)^{-2}. It is not the pointwise sum at the zeros.

### Gaps
- I did not access the primary papers CGG 1984 (Bull. LMS 16), CGG 1986 (Mathematika 33), CGG 1998 (Proc. LMS 76), Montgomery–Odlyzko (Colloq. Math. Soc. János Bolyai 34, Budapest 1981) or CGGGH 1985 (QJM 36). Their content is reported via BMN, Bui, Feng–Wu, Bui–Heath-Brown and Ng. In particular, the "c ≥ 6.2" statement, and whether it is uniform over all coefficients or over a class, is BMN's summary and was not checked in CGG 1984.
- I did not verify the error terms these papers state for M_2(c) when K = T(log T)^{-2}, or whether any of them treat K ≍ T.
- I did not examine Hall's Wirtinger papers (J. Number Theory 2002; Mathematika 2005) or Bredberg's paper. I found no evidence that they use discrete means of Dirichlet polynomials over zeros. Bui describes Hall's results as unconditional, which is consistent with a continuous-mean method, but this is unverified.

## 3. Explicit "Lemma: assume RH, Σ_{0<γ≤T} |Σ_{n≤N} a_n n^{-ρ}|² = …" statements in the ζ'(ρ) literature

### Takeaway
There are several explicit statements, all under RH:
- Ng (2008): θ < 1 with o(T) error and coefficients ≪ T^ε.
- Milinovich–Ng (2012): the Möbius case for every fixed ϑ < 1, by a residue-theorem method rather than Landau–Gonek, with a method error O(ξ·log² T).
- Milinovich (2010): an upper bound for ξ ≤ T/log T.
- Çiçek (2021) and Kirila (2020): short prime polynomials.
- Radziwiłł (2014): upper bounds up to N^k ≤ T.
- Bui–Florea–Milinovich (2023): general x with error O(x·log²(xT)·Σ|a|²/n).

None of these gives a lower bound in the regime T ≍ N. Twisted versions with ζ'(ρ) or ζ(ρ+α) need N < T^{1/2}.

### Cited Findings
- **Ng, "Extreme values of ζ'(ρ)", Proposition 4(i).** Let A(s) = Σ_{n≤M} x_n n^{-s} with real x_n, and polynomial length governed by y = T^θ. "Suppose that |x_n| ≪ T^ε and θ < 1. Then
  S_2 = Σ_{0<γ<T} |A(ρ)|² = N(T)·Σ_{m≤M} x_m²/m − (T/π)·Σ_{m≤M} (Λ∗x)(m)·x_m/m + o(T)."
  - Ng notes: "The formula for S_2 in (i) is mentioned without proof on page 6 of [CGGGH, QJM 36 (1985) 43–51]. It can be proven by following the argument of [Ng, Duke 125 (2004)] Lemma 3."
  - The twisted sum S_1 = Σ ζ'(ρ)|A(ρ)|² (part (ii)) requires θ < 1/2, from Ng's preprint "Discrete mean values of the Riemann zeta function and Dirichlet polynomials", Theorem 1.3.

  — [Ng, arXiv:0706.1765](https://arxiv.org/abs/0706.1765)
- **Milinovich–Ng (Lower bounds for moments of ζ'(ρ)), Lemma 2.** For x_n, y_n ≪ τ_ℓ(n) and 0 < ϑ < 1/2, the twisted sum S(X,Y;T) has an asymptotic with error O_A(T(log T)^{-A} + T^{3/4+ϑ/2+ε}). The term T^{3/4+ϑ/2+ε} forces ϑ < 1/2. The lemma is "a special case of Theorem 1.3 of Ng". The paper also uses the Landau–Gonek formula (its Lemma 3) to bound the pure Dirichlet-polynomial sum. — [Milinovich–Ng, arXiv:0706.2321](https://arxiv.org/abs/0706.2321)
- **Milinovich–Ng, "A note on a conjecture of Gonek" (Funct. Approx. 46.2 (2012)), Proposition.** Assume RH, let 0 < ϑ < 1 be fixed, ξ = T^ϑ and M_ξ(s) = Σ_{n≤ξ} μ(n) n^{-s}. Then
  M_2 = Σ_{0<γ≤T} |M_ξ(ρ)|² = (3/π³)·(ϑ + ϑ²)·T·log² T + O(T log T).
  - **Method:** the residue theorem applied to M_ξ(s)·M_ξ(1−s)·ζ'/ζ(s), with the Montgomery–Vaughan/Tsang mean-value theorem
    ∫_0^T (Σ a_n n^{-it})·(Σ b̄_n n^{it}) dt = T·Σ a_n b̄_n + O((Σ n|a_n|²)^{1/2}·(Σ n|b_n|²)^{1/2}).
  - **Pieces:**
    - The horizontal segments and the zeros in [T, T+1] cost O(ξ·(log T)²). This uses |M_ξ(σ+it)| ≪ ξ^{1−σ} and ζ'/ζ(σ+iT) ≪ (log T)² on a well-chosen T.
    - K = (3/π³)·T·log(T/2π)·log ξ + O(T log T).
    - The Landau-type piece contributes +(3/π³)·T·(log ξ)².
  - **Sign of the Landau piece:** for Möbius coefficients the off-diagonal adds ϑ² rather than subtracting it. Their displayed (4.4), "J_1 = −(3/2π³)·T·(log ξ)²", has a sign inconsistent with its own derivation: J_1 = −((T−1)/2π)·Σ α_n μ(n)/n with Σ α_n μ(n)/n = −(3/π²)(log ξ)², which gives +. The final (2.3) is as stated.
  - **Novelty claim:** "A novel aspect of our approach is that it does not require the use of the Guinand–Weil explicit formula or of the Landau–Gonek explicit formula … it is likely that it can be extended to evaluate the discrete mean (2.6) for a large class of coefficients a_n when ξ ≤ T."
  - **Application:** the Theorem Σ 1/|ζ'(ρ)|² ≥ (3/(2π³) − ε)·T (RH and simple zeros) is obtained by letting ϑ → 1⁻ in a Cauchy–Schwarz bound.

  — [Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)
- **Milinovich, Lemma 4.2 (upper bound).** "Assume the Riemann Hypothesis … m_ξ = max(1, max_{1≤n≤ξ} |a_n|). Then for 3 ≤ ξ ≤ T(log T)^{-1} and any complex number α with Re α ≥ 0 we have Σ_{0<γ≤T} |Σ_{n≤ξ} a_n/n^{ρ+α}|² ≪ m_ξ·T·log T·Σ_{n≤ξ} |a_n|/n, where the implied constant is absolute." The proof applies Landau–Gonek. The Landau term Σ_1 is bounded in absolute value (≪ m_ξ T log T·Σ|a_n|/n) and not used as a cancellation. — [Milinovich, arXiv:0806.0786](https://arxiv.org/abs/0806.0786)
- **Çiçek, Lemma 3.2.** "Assume RH. Let k be a positive integer and suppose 1 < Y ≤ (T/log T)^{1/(3k)}. For any complex-valued sequence (a_p) …
  Σ_{0<γ≤T} |Σ_{p≤Y} a_p/p^{1/2+iγ}|^{2k} ≪ k!·N(T)·(Σ_{p≤Y} |a_p|²/p)^k."
  It is derived from Lemma 3.1 (see Section 1). — [Çiçek, arXiv:2007.10533](https://arxiv.org/abs/2007.10533)
- **Kirila on the sign of the secondary term.** On RH, Kirila summarises Landau–Gonek as Σ_{0<γ≤T} e^{irγ} = N(T)·δ_0(r) − T·f(r) + small error, "where f is a certain nonnegative function". He adds: "The final contribution to J_k(T) from this secondary term is possibly of the same order as that of the first term … However, the secondary term contribution is not positive, so we may ignore it and still obtain an upper bound." Kirila's Theorem 1.1 is J_k(T) ≪_k (log T)^{k(k+2)} on RH for all k > 0. — [Kirila, arXiv:1804.08826](https://arxiv.org/abs/1804.08826)
- **Radziwiłł, Lemma 9 (upper bound up to length T).** For the prime-power polynomial B_N(s) of his Lemma 2: "If N^k ≤ T then Σ_{T≤γ≤2T} |B_N(1/2+iγ)|^{2k} ≪ (Ck)^k·T·log T·(log N)^{2k}." Lemma 4 and Lemma 5 use the condition N^k ≤ T/log T. — [Radziwiłł, arXiv:1301.3232](https://arxiv.org/abs/1301.3232)
- **Bui–Florea–Milinovich Theorem 3.1.** The general RH statement for any x ≥ 2 and T > 1 (see Section 1) was used for upper bounds on negative moments Σ_{T<γ≤2T} |ζ'(ρ)|^{-2k} over a full-density subfamily of zeros. — [BFM, arXiv:2310.03949](https://arxiv.org/abs/2310.03949)
- **Benli–Elma–Ng (2023).** They estimate Σ_{0<Im ρ≤T} ζ(ρ+α)·X(ρ)·Y(1−ρ) with X, Y of length N ≪ T^ϑ, ϑ < 1/2. "In the conditional case, in order to establish an asymptotic formula for general Dirichlet coefficients, we must have N < T^ϑ with ϑ < (1−Θ)/(5/2 − Θ + δ_1 + 2δ_2)." Application: on RH, Σ |ζ^{(m)}(ρ)|^{2k} ≫ T(log T)^{k²+2km+1}. — [Benli–Elma–Ng, arXiv:2311.13554](https://arxiv.org/abs/2311.13554)

### Inferences
- **Summary of ranges for pure Dirichlet-polynomial sums under RH:**
  - θ < 1 fixed, error o(T) (Ng);
  - ϑ < 1 fixed for Möbius coefficients, error O(T log T) against a T log² T main term (Milinovich–Ng);
  - any x, error O(x log²(xT)·Σ|a|²/n) (BFM);
  - upper bounds to ξ ≤ T/log T (Milinovich) and N^k ≤ T (Radziwiłł).

  Twisted sums with ζ' or ζ(ρ+α) are restricted to lengths below T^{1/2}.
- **The residue method at ξ = T/C.** In the Milinovich–Ng residue method the obstruction is the O(ξ·log² T) cost of the horizontal segment at height T. At ξ = T/C this is ≍ T·log² T/C against a main term (6/π³)·T·log² T in the Möbius case. A large but inexplicit constant C might therefore suffice for those coefficients. For general coefficients the trivial bound |A(σ+it)·A(1−σ−it)| ≲ N·Σ|a|²/n makes the cost ≍ N·log² T·Σ|a|²/n, the same as BFM's error. This is my reading of their proof, not a stated result.

### Gaps
- I did not see Ng's preprint "Discrete mean values of the Riemann zeta function and Dirichlet polynomials" (cited as submitted, c. 2007), its Theorem 1.3, or its publication status.
- I did not read Ng's Duke 2004 Lemma 3 directly.
- I did not verify the journal details for Ng's "Extreme values" (JLMS 2008 per the brief), Milinovich–Ng "Lower bounds" (IMRN 2014 per the brief), Kirila (Mathematika 2020 per the brief), Bui–Heath-Brown or Feng–Wu. arXiv versions were used.
- No paper found states a two-sided version (an asymptotic or a lower bound) of Σ|A(ρ)|² at N ≍ T for general coefficients.

## 4. Upper bounds: large sieve / Montgomery–Vaughan type bounds over zeros

### Takeaway
The verified statements are of two kinds:
- Well-spaced-point large sieve bounds: (T + 2πN)·log(2N)·‖a‖² for 1-spaced points (IK Theorem 9.4), and Montgomery's (N + R·T^{1/2})·log(2T)·‖a‖².
- Zero-specific bounds: Milinovich (ξ ≤ T/log T), Radziwiłł (N^k ≤ T, plus a large sieve at spacing δ/log T), and BFM's Theorem 3.1, which implies ≪ (T log T + N log²(NT))·Σ|a|²/n.

The continuous two-sided mean-value theorem (T − 2πN)‖a‖² ≤ ∫_0^T |D|² ≤ (T + 2πN)‖a‖² is the natural analogue of the user's inequality. I could not verify the exact "(T+N) log T" statements attributed to Montgomery (Topics, 1971), Ramachandra or Jutila.

### Cited Findings
- **Montgomery's continuous two-sided theorem.** "[Montgomery, Ten Lectures (1994), §7.2, Theorem 1] Let D be a Dirichlet polynomial of length N with coefficients a. Then (T − 2πN)·‖a‖²_2 ≤ ‖D(it)‖²_{L²[0,T]} ≤ (T + 2πN)·‖a‖²_2." — [Harrison, Warwick reading-group notes "Mean value estimates II" (2025)](https://warwick.ac.uk/fac/sci/maths/people/staff/josephharrison/dirichlet_polynomials_week_4_notes.pdf)
- **Discrete version for well-spaced points.**
  - Gallagher's lemma: for 1/2 < t_1 < … < t_n < T − 1/2 well-spaced (|t − s| < 1 ⇒ t = s), Σ_i |f(t_i)|² ≤ ∫_0^T (|f|² + |f f'|).
  - "[Iwaniec–Kowalski, Theorem 9.4] … If µ is a counting measure supported on [0,T], then ‖D(it)‖²_{L²(µ)} ≤ (T + 2πN)·log(2N)·‖a‖²_2", in the notes' well-spaced setting.
  - Montgomery's bound for R well-spaced points (Theorem 2.7 of the notes): ‖D(it)‖²_{L²(µ)} ≪ (N + R·T^{1/2})·log(2T)·‖a‖²_2.

  — [Harrison notes](https://warwick.ac.uk/fac/sci/maths/people/staff/josephharrison/dirichlet_polynomials_week_4_notes.pdf)
- **Continuous mean-value theorem with cross terms (Montgomery–Vaughan / Tsang).** ∫_0^T (Σ a_n n^{-it})·(Σ b̄_n n^{it}) dt = T·Σ a_n b̄_n + O((Σ n|a_n|²)^{1/2}·(Σ n|b_n|²)^{1/2}). This is "Lemma 1 of Tsang [Acta Arith. 46 (1986)]; the special case b_n = a_n is originally due to Montgomery and Vaughan [J. LMS (2) 8 (1974) 73–82]". — [Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)
- **Radziwiłł's large sieve near the critical line, Lemma 3.**
  - **Hypotheses:** A has positive coefficients and length x; points s_r = σ_r + i·t_r with T ≤ t_r ≤ 2T and 0 ≤ σ_r − 1/2 ≤ ε/log T; |t_i − t_j| ≥ δ/log T with 100ε < δ < 1; and x^k ≤ T.
  - **Conclusion:** Σ_r |A(s_r)|^{2k} ≤ (20·log T/δ)·∫_{−2T}^{2T} |A(1/2+it)|^{2k} dt.
  - **Proof:** a majorant principle, valid because D = A^k has positive coefficients and length ≤ T.

  — [Radziwiłł, arXiv:1301.3232](https://arxiv.org/abs/1301.3232)
- **Milinovich Lemma 4.2:** ≪ m_ξ·T·log T·Σ|a_n|/n for ξ ≤ T/log T, under RH (see Section 3). — [Milinovich](https://arxiv.org/abs/0806.0786)

### Inferences
- **Gallagher at the scale of zeros.** There are O(log T) zeros in any unit interval. Applying Gallagher's lemma to the zero-counting measure gives Σ_{0<γ≤T} |Σ_{n≤N} b_n n^{-iγ}|² ≪ log T·(T + N)·log N·Σb², with no RH needed.
- **The RH bound from BFM.** Theorem 3.1 combined with the Schur bound on the Landau form (Section 6) gives Σ_{0<γ≤T} |Σ b_n n^{-iγ}|² ≤ (T/π)·log T·(1 + o(1))·Σb² + O(N·log²(NT)·Σb²). Up to one log on the N-term, this is the "(T + N) log T" shape the brief asks about.

### Gaps
- I could not access Montgomery, Topics in Multiplicative Number Theory (LNM 227, 1971), so I could not quote its large-sieve statement for zeros.
- I found no primary statement from Ramachandra or Jutila of a bound Σ_{0<γ≤T} |Σ a_n n^{-iγ}|² ≪ (T + N)·log T·Σ|a_n|². This remains unverified.
- I did not check Iwaniec–Kowalski Theorem 9.4 against the book itself. The spacing hypothesis is as stated in Harrison's notes.

## 5. "Sampling", "frame" or "Marcinkiewicz–Zygmund" statements and lower bounds Σ_γ |A(ρ)|² ≫ …

### Takeaway
I found no paper that calls the zeta zeros a sampling set, frame or Marcinkiewicz–Zygmund family for Dirichlet polynomials. I also found none that states a lower bound Σ_γ |A(ρ)|² ≥ c·T·Σ|a|²/n uniform in the coefficients. The nearest results are listed below; each is either averaged over a window, restricted to specific coefficients, or limited to N ≤ T^{1−δ} or T/log² T.

### Cited Findings
- **Searches with no hits.** I searched for "sampling", "frame", "Marcinkiewicz–Zygmund", "Beurling density" or "Paley–Wiener" together with zeta zeros and Dirichlet polynomials (general web and the arXiv API). I found no such paper; the results were only Beurling-zeta zero-density papers and Nyman–Beurling-type criteria. — e.g. [arXiv:1704.01234](https://arxiv.org/abs/1704.01234), [arXiv:2012.09045](https://arxiv.org/abs/2012.09045)
- **Uniform-in-coefficients bound for the α-averaged sum.** CGG (1984), as reported by BMN, show h(c) > 1 for c ≥ 6.2, where M_2(c)/M_1 = h(c) + o(1) for polynomials of length K = T(log T)^{-2}. — [BMN](https://arxiv.org/abs/0910.2052)
- **Specific coefficients, all ϑ < 1.** Milinovich–Ng's Möbius computation gives Σ_{0<γ≤T} |M_ξ(ρ)|² = (3/π³)(ϑ + ϑ²)·T·log² T + O(T log T) for each fixed ϑ < 1. In the Rudnick–Soundararajan / Cauchy–Schwarz method they use it as an upper bound on the denominator. — [Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)
- **Lower bounds for discrete moments of ζ', not of Dirichlet polynomials.** Examples are Milinovich–Ng (0706.2321) and Benli–Elma–Ng (2311.13554). They use Dirichlet polynomials of length < T^{1/2} as Rudnick–Soundararajan "test functions". — [Milinovich–Ng](https://arxiv.org/abs/0706.2321); [Benli–Elma–Ng](https://arxiv.org/abs/2311.13554)

### Inferences
- **What would be new.** A pointwise, log-free, coefficient-uniform lower bound at T ≥ C·N does not appear in the literature I could access. The user's inequality, if correct, goes beyond every stated range: N ≤ T^{1−δ} (Ng), K ≤ T(log T)^{-2} (MO/BMN, α-averaged), and N ≤ T/log^{2+ε} T (the lower bound implied by BFM's Theorem 3.1).
- **Density heuristic (not sourced as a theorem).** Zeros near height T have density (1/2π)·log(T/2π). A length-N Dirichlet polynomial has frequencies log n ∈ [0, log N]. A Nyquist/Beurling–Landau analogy then suggests sampling should need log(T/2π) > log N, i.e. T > 2πN. This matches both the 2πN in Montgomery's continuous theorem and the counterexample in Section 6.

### Gaps
- I may have missed harmonic-analysis papers (Seip, Olevskii–Ulanovskii, Kahane-type sampling) that treat {γ} as sampling sets for almost-periodic or Dirichlet-polynomial spaces. None appeared in my searches.
- I did not examine Hall's Wirtinger method or Bredberg at all.

## 6. The regime T ≍ N: what the known results give at T = C·N, and the Landau-term cancellation

### Takeaway
At T = C·N none of the published statements gives anything. Their error terms (BFM: O(N·log²(NT)·Σb²); Çiçek: worse; Ng: needs θ < 1; MO/BMN: K ≤ T/log² T) are larger than the possible size of the main term there.

The main term N(T)·Σb² − (T/π)·Re Σ b_m·b̄_{mk}·Λ(k)/√k is still informative. An elementary Schur/Mertens bound shows it is always ≥ (T/2π)·[log(T/(2πN)) − O(1)]·Σb², and ζ-like coefficients b_n = n^{-1/2} attain this. So the Landau term can cancel all of the diagonal except log(T/N). A log-free bound c·T·Σb² is therefore the correct order when T/N is a large constant, and it must fail for T < 2πN. The user's threshold e^24 and constant 1/100 are consistent with this picture.

### Cited Findings
- **The off-diagonal term in the literature.**
  - BFM: −(T/π)·Re Σ_{kn≤x} a_{kn}·ā_n·Λ(k)/(kn). — [BFM](https://arxiv.org/abs/2310.03949)
  - Ng: −(T/π)·Σ (Λ∗x)(m)·x_m/m. — [Ng](https://arxiv.org/abs/0706.1765)
  - Çiçek: −(T/π)·Re Σ a_n·ā_m·(m/n)^{iv}·Λ(m/n)/√(m/n). — [Çiçek](https://arxiv.org/abs/2007.10533)
  - MO/CGG: the term subtracted in h(c). — [BMN](https://arxiv.org/abs/0910.2052)
- **Papers that note it can be as large as the diagonal.**
  - Kirila: "possibly of the same order as that of the first term … the secondary term contribution is not positive". — [Kirila](https://arxiv.org/abs/1804.08826)
  - BMN: test polynomials approximating ζ(1/2+it)^r are chosen "to make A(t) small … near the zeros", and h(c) < 1 for every coefficient choice when c < 1/2 (CGG 1984). — [BMN](https://arxiv.org/abs/0910.2052)
  - For Möbius coefficients the same term instead adds (3/π³)·T·log² ξ. — [Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)
- **Polynomial lengths actually used in published discrete-mean arguments:**
  - K = T(log T)^{-2} (MO, BMN, Feng–Wu) — [BMN](https://arxiv.org/abs/0910.2052), [Feng–Wu](https://arxiv.org/abs/1003.0752)
  - T^{1−ε} (CGG 1984) — [Bui](https://arxiv.org/abs/0903.4007)
  - T^θ with θ < 1 (Ng; Milinovich–Ng 2012) — [Ng](https://arxiv.org/abs/0706.1765), [Milinovich–Ng 2012](http://home.olemiss.edu/~mbmilino/Gonek's%20Conjecture.pdf)
  - ξ ≤ T/log T, upper bound only (Milinovich) — [Milinovich](https://arxiv.org/abs/0806.0786)
  - N^k ≤ T, upper bound only (Radziwiłł) — [Radziwiłł](https://arxiv.org/abs/1301.3232)
  - M, N ≤ T stated, but with off-diagonal errors (Çiçek) — [Çiçek](https://arxiv.org/abs/2007.10533)
  - < T^{1/2} for twisted sums (CGG 1998 / Bui–Heath-Brown; Benli–Elma–Ng) — [Bui–Heath-Brown](https://arxiv.org/abs/1302.5018), [Benli–Elma–Ng](https://arxiv.org/abs/2311.13554)
- **A related transition at X ≍ T.** Durkan–Hughes–Pearce-Crump study S(X,T) = Σ_{T<γ≤2T} χ(ρ)X^ρ, where χ is the functional-equation factor.
  - Their Theorem 5, "an oscillatory analogue" of Gonek's theorem, is uniform in X and T. Its case distinctions fall at X ≍ T (thresholds T/2π and T/π as extracted).
  - Corollary 5.2, for integers X = o(T): Σ_{0<γ≤T} χ(ρ)X^ρ = −T/2π + O(X log X) + O(T^{1/2}(log T)²) under RH.

  — [DHP, arXiv:2601.18025](https://arxiv.org/abs/2601.18025)
- **Error terms dominate for length-T polynomials.** DHP report that Hughes, Martin and Pearce-Crump (2023) proposed "a simple heuristic which gives the correct main term … but with an error term that dominates the main term".
  - The heuristic writes ζ^{(ν)}(σ+it) = (−1)^ν·Σ_{m≤t} (log m)^ν/m^{σ+it} + O(t^{−σ}(log t)^ν), a Dirichlet polynomial of length ≍ t. It then sums over zeros with Gonek's Corollary 2.1, and "they showed the error terms dominate, so the argument is heuristic, not rigorous."
  - DHP's aim is to use both pieces of the approximate functional equation via S(X,T), "making the heuristic rigorous".
  - This is an explicit literature statement that the Landau–Gonek route breaks down for Dirichlet polynomials of length comparable to the height.

  — [DHP, arXiv:2601.18025](https://arxiv.org/abs/2601.18025)

### Inferences
These are my derivations, not taken from a source.

- **Landau-form bound (Schur test with weights n^{-1/2}).** For Q(b) = 2·Re Σ_{mk≤N} b_m·b̄_{mk}·Λ(k)/√k:
  - The row sum at m is m^{-1/2}·[Σ_{k≤N/m} Λ(k)/k + Σ_{k|m} Λ(k)] = m^{-1/2}·[log N + O(1)] (Mertens, and Σ_{k|m} Λ(k) = log m).
  - Hence |Q(b)| ≤ (log N + O(1))·Σb².
  - With N(T) = (T/2π)·log(T/2π) − T/2π + O(log T), the main term satisfies
    N(T)·Σb² − (T/2π)·Q(b) ≥ (T/2π)·[log(T/(2πN)) − O(1)]·Σb².
  - The bound is sharp: b_n = n^{-1/2} (a(n) ≡ 1) gives Q = log² N + O(log N) against Σb² = log N + O(1).
  - So at T = C·N the best possible uniform main-term lower bound is ≍ (T/2π)·log C·Σb², which is log-free.
- **Necessity of C ≳ 2π (counterexample).** Take a(n) ≡ 1, N = x, T ≤ (2π − ε)·N.
  - The Hardy–Littlewood approximation (Titchmarsh, Theorem 4.11: ζ(s) = Σ_{n≤x} n^{-s} − x^{1−s}/(1−s) + O(x^{-σ}) for |t| < 2πx/C, C > 1) applies at every zero with |γ| ≤ T.
  - At a zero it gives Σ_{n≤N} n^{-ρ} = N^{1−ρ}/(1−ρ) + O(N^{-1/2}).
  - Hence Σ_{|γ|≤T} |A(ρ)|² ≪ N·Σ_γ |ρ|^{-2} + N(T)/N ≪ N.
  - The right side of the user's inequality is (T/100)·Σ_{n≤N} 1/n ≍ N log N.
  - So no inequality of the user's form can hold for T ≤ (2π − ε)·N and large N; some threshold C ≥ 2π is necessary.
  - The user's hypothesis T ≥ e^24·N is far beyond this, so there is no conflict. The main-term heuristic needs log C > log 2π + 1 + O(1), and C = e^24 leaves a margin of about 21 in the logarithm.
- **What the literature gives for T between C·N and N log N.**
  - **BFM:** error ≍ N·log²(NT)·Σb², which is ≥ T·Σb² throughout T ≤ N·log² N. So BFM gives nothing here, and the residue method of Milinovich–Ng loses the same O(N·log² T).
  - **Ng (θ < 1) and MO/BMN (K ≤ T/log² T):** these exclude the regime by hypothesis.
  - **Where a lower bound does follow:** from BFM Theorem 3.1 plus the Schur bound, Σ_{0<γ≤T} |Σ b_n n^{-iγ}|² ≥ (T/2π)·(log(T/N) − O(1))·Σb² once N ≤ c·T/log² T, which is ≫ T·log log T·Σb² there.
  - **Conclusion:** within the published results, a log-free sampling bound uniform in the coefficients is only reachable for N ≤ T/log² T. The regime T ∈ [C·N, N·log² N], which contains the user's T ≍ N, is not covered by any statement I found.

### Gaps
- I could not check whether any of Gonek 1993, CGGGH 1985, Montgomery–Odlyzko 1981/84 or Ng's discrete-mean-values preprint treats N ≍ T or remarks that the main term degenerates to (T/2π)·log(T/2πN) at N = T^{1−o(1)}. The papers I read do not make this remark in that form; the nearest are Kirila's and BMN's.
- I found no source using a smoothed (Selberg-minorant or Guinand–Weil) cutoff to get a log-free lower bound at T ≍ N. If one exists, it would be the direct precursor of the user's result.
