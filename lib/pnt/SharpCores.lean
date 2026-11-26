import SharpChainU
import AuxPrimes
import SlopeFExact

/-!
# The pieces (T) and (F) + (V) for the construction

The pieces `SharpPieces.primes` and `SharpPieces.slopeFV` of the proof's architecture (`SharpInputs`), proved for the
construction `sharpCons` with `adm := fun Dg => Dg.Adm` (`SharpAdm`): `sharpPrimes` and `sharpSlopeFV`.

**(T)** (`sharpPrimes`). `ShortNorm` gives a constant `c > 0` with a prime `T` of the shape `ArithT` and
`Λ_u < log T ≤ Λ_u + log 2` once `log(4dM²) ≤ c√Λ_u` (`SharpDesign.exists_prime_arithT`). At an admissible design
`(log 4dM²)³ ≤ Λ_u` (`Adm.logM_cube_le`) and `Λ_u ≥ 16mx^ε ≥ √x` (`Adm.lam_ge`, `Adm.m_mul_rpow`), so the condition
holds once `c⁶Λ_u ≥ 1`, at every `x ≥ c^{−12}`: then `Y² ≤ c²Λ_u` for `Y = log 4dM²`, as else
`c⁶Λ_u³ < Y⁶ ≤ Λ_u²`. The auxiliary prime `sharpT` is then the least such prime, and `c_T = 0`.

**(F) + (V)** (`sharpSlopeFV`), at every admissible design, from the exact slope bound `SharpObj.slopeFV_exact`.
* `SG` has a place over each split prime (`exists_sharpSG`): `π_g·conj π_g = g` (`normPi_mul_conj`), and `conj π_g`
  is a nonzero non-unit, as `g ≥ 2` is not a unit of `O_E` (`not_isUnit_natCast`: `N(g·O_E) = g^{[E:ℚ]}`), so it lies
  in a maximal ideal, which lies over `g` (`exists_mem_placesOf_conj`).
* `X_c = ⊤`, and the step-0 weights are antitone (`Setting.Ranks.wt0_antitone`).
* **The budget** (`cFx_le`): the exact constant `3|ν| log k + 2(Σλ)⁺ Σ_{P∈ST} log N(P)/(k[E:ℚ]) + |ST| log 2` is at
  most `x^{4ε}Σ_t a_t/8`. With `A = Σ_t a_t`: `|ν|, (Σλ)⁺ ≤ 2A` (`Adm.sum_natW_le`, `Adm.sum_wt0_le`; the base word's
  family is `hc u`, pinned to `u`), `log k ≤ 6 log x ≤ 6x^ε/1000`; every place of `ST` contains `T`
  (`natCast_mem_of_conj_normPi_mem`), so `|ST| log 2 ≤ Σ_{P∈ST} log N(P) ≤ [E:ℚ] log T` (`sum_log_absNorm_le`), with
  `log T ≤ x` (`log_sharpT_le`), `x ≤ k` and `[E:ℚ]·x ≤ A` (`Adm.card_E_le`). So the constant is at most
  `36A log x + 4A + A ≤ (0.036x^ε + 5)A ≤ x^εA/8`, as `x^ε ≥ 4096`.
-/

namespace ZetaBalance

open NumberField IsDedekindDomain

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-! ## Places over an element -/

/-- **A place of `placesOf z` lies over `z`.** -/
theorem mem_of_mem_placesOf {z : 𝓞 S.E} {v : HeightOneSpectrum (𝓞 S.E)} (hv : v ∈ placesOf z) :
    z ∈ v.asIdeal := by
  unfold placesOf at hv
  split_ifs at hv with h
  · simpa using hv
  · simp at hv

/-- **Every place over `z ≠ 0` is in `placesOf z`**: those places divide `z·O_E ≠ 0`, so are finitely many
(`Ideal.finite_factors`). -/
theorem mem_placesOf_of_mem {z : 𝓞 S.E} (hz : z ≠ 0) {v : HeightOneSpectrum (𝓞 S.E)} (hv : z ∈ v.asIdeal) :
    v ∈ placesOf z := by
  have hfin : {v : HeightOneSpectrum (𝓞 S.E) | z ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {z}) (by simpa using hz)).subset fun v hv => by
      simpa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using hv
  rw [placesOf, dite_eq_left hfin, Set.Finite.mem_toFinset]
  exact hv

/-! ## Elements of norm `p` -/

/-- **`π·conj π = p`** where `π = normPi S M p` is a `halfO` (`Setting.halfO_mul_conj_eq`). -/
theorem normPi_mul_conj {M p : ℕ}
    (h : S.d % 4 = 3 ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]) :
    normPi S M p * IsCMField.ringOfIntegersComplexConj S.E (normPi S M p) = p := by
  rw [normPi, dite_eq_left h]
  exact Setting.halfO_mul_conj_eq _ _ _ h.2.choose_spec.choose_spec.1

/-- **`p` lies in every place over `conj π`**, `π = normPi S M p`: `π·conj π = p` (`normPi_mul_conj`), and
otherwise `conj π = 1` lies in no place. -/
theorem natCast_mem_of_conj_normPi_mem {M p : ℕ} {v : HeightOneSpectrum (𝓞 S.E)}
    (hv : IsCMField.ringOfIntegersComplexConj S.E (normPi S M p) ∈ v.asIdeal) : (p : 𝓞 S.E) ∈ v.asIdeal := by
  by_cases h : S.d % 4 = 3 ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]
  · rw [← normPi_mul_conj h]
    exact v.asIdeal.mul_mem_left _ hv
  · rw [normPi, dite_eq_right h, map_one] at hv
    exact absurd ((Ideal.eq_top_iff_one _).2 hv) v.isPrime.ne_top

/-- **`p ≥ 2` is not a unit of `O_E`**: `N(p·O_E) = p^{[E:ℚ]} ≠ 1` (`Ideal.absNorm_span_natCast`). -/
theorem not_isUnit_natCast {p : ℕ} (hp : 2 ≤ p) : ¬IsUnit (p : 𝓞 S.E) := fun hu => by
  have h := Ideal.absNorm_span_natCast (S := 𝓞 S.E) p
  rw [Ideal.span_singleton_eq_top.2 hu, Ideal.absNorm_top] at h
  have := Nat.one_lt_pow (Module.finrank_pos (R := ℤ) (M := 𝓞 S.E)).ne' (by omega : 1 < p)
  omega

/-- **A place over `conj π` and `p`**, `π = normPi S M p` a `halfO` of norm `p ≥ 2`: `conj π ≠ 0`, and it is not a
unit (else so would be `π` and `p = π·conj π`, against `not_isUnit_natCast`), so it lies in a maximal ideal, a place
of `placesOf (conj π)` over `p` (`natCast_mem_of_conj_normPi_mem`). -/
theorem exists_mem_placesOf_conj {M p : ℕ} (hp : 2 ≤ p)
    (h : S.d % 4 = 3 ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + S.d * b ^ 2 ∧ (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]) :
    ∃ v ∈ placesOf (IsCMField.ringOfIntegersComplexConj S.E (normPi S M p)), (p : 𝓞 S.E) ∈ v.asIdeal := by
  set c := IsCMField.ringOfIntegersComplexConj S.E
  have hπ := normPi_mul_conj h
  have hz : c (normPi S M p) ≠ 0 := fun h0 => by
    rw [h0, mul_zero, eq_comm, Nat.cast_eq_zero] at hπ
    omega
  have hu : ¬IsUnit (c (normPi S M p)) := fun hu => not_isUnit_natCast hp (by
    rw [← hπ]
    exact ((isUnit_map_iff c _).1 hu).mul hu)
  obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.2 hu)
  have hmem : c (normPi S M p) ∈ P := hle (Ideal.mem_span_singleton_self _)
  let v : HeightOneSpectrum (𝓞 S.E) := ⟨P, hPm.isPrime, fun hb => hz (by rwa [hb, Ideal.mem_bot] at hmem)⟩
  exact ⟨v, mem_placesOf_of_mem hz hmem, natCast_mem_of_conj_normPi_mem hmem⟩

/-- **`SG` has a place over `g₀` and one over `g₁`** at an admissible design: A11 gives `π_g` of norm `g`, with
`d ≡ 3 (mod 4)` from `d ≡ 7 (mod 16)` (`exists_mem_placesOf_conj`). -/
theorem exists_sharpSG {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm) :
    (∃ w : sharpSG Dg, (Dg.g₀ : 𝓞 S.E) ∈ w.1.asIdeal) ∧ ∃ w : sharpSG Dg, (Dg.g₁ : 𝓞 S.E) ∈ w.1.asIdeal := by
  classical
  have hd : S.d % 4 = 3 := by have := hA.d_mod; omega
  have key : ∀ g ∈ [Dg.g₀, Dg.g₁], g.Prime → ∃ v ∈ placesOf (IsCMField.ringOfIntegersComplexConj S.E
      (normPi S S.N g)), (g : 𝓞 S.E) ∈ v.asIdeal := fun g hg hgp =>
    exists_mem_placesOf_conj hgp.two_le ⟨hd, (hA.split g hg).2.2⟩
  obtain ⟨v₀, h₀, hg₀⟩ := key Dg.g₀ (by simp) Dg.g₀_prime
  obtain ⟨v₁, h₁, hg₁⟩ := key Dg.g₁ (by simp) Dg.g₁_prime
  exact ⟨⟨⟨v₀, Finset.mem_union_left _ h₀⟩, hg₀⟩, ⟨v₁, Finset.mem_union_right _ h₁⟩, hg₁⟩

/-! ## (T) -/

/-- **(T) for the construction** (`SharpPieces.primes` at `adm := Adm`, `cons := sharpCons`): from `ShortNorm`'s
constant `c`, at every `ε` and every admissible design at `x ≥ c^{−12}`, the window of `sharpT` holds a prime of the
shape `ArithT` (`SharpDesign.exists_prime_arithT`, as `log 4dM² ≤ c√Λ_u`), so `sharpT` is one, with
`Λ_u < log T` and `c_T = 0`. -/
theorem sharpPrimes (hS : ShortNorm) : EventuallyAdm (fun Dg => Dg.Adm)
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((sharpCons Dg).obj u).Primes u := by
  classical
  obtain ⟨c, hc, H⟩ := SharpDesign.exists_prime_arithT hS
  refine ⟨1, one_pos, fun ε _ _ => ⟨((c ^ 6)⁻¹) ^ 2, fun {S κ x X} Dg hx hA u _ => ?_⟩⟩
  set Λ := S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁))
  set Y := Real.log (4 * S.d * ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℝ) ^ 2)
  have hc6 : 0 < c ^ 6 := by positivity
  -- `Λ_u ≥ 16mx^ε ≥ √x ≥ c^{−6}`
  have h1 : 1 ≤ c ^ 6 * Λ := by
    have hm := hA.m_mul_rpow.1
    rw [← Real.sqrt_eq_rpow] at hm
    have hl := hA.lam_ge u
    have hmx : 0 ≤ (Dg.m : ℝ) * x ^ ε := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hA.big.pos.le _)
    have hsx : (c ^ 6)⁻¹ ≤ √x := (Real.le_sqrt (by positivity) hA.big.pos.le).2 hx
    calc 1 = c ^ 6 * (c ^ 6)⁻¹ := (mul_inv_cancel₀ hc6.ne').symm
      _ ≤ c ^ 6 * Λ := by gcongr; linarith
  have hΛ0 : 0 < Λ := pos_of_mul_pos_right (one_pos.trans_le h1) hc6.le
  -- `log 4dM² ≤ c√Λ_u`: else `c⁶Λ³ < Y⁶ ≤ Λ²`
  have hYc : Y ≤ c * √Λ := by
    rcases le_or_gt Y 0 with hY0 | hY0
    · exact hY0.trans (by positivity)
    have hY3 : Y ^ 3 ≤ Λ := hA.logM_cube_le u
    have key : Y ^ 2 ≤ c ^ 2 * Λ := by
      by_contra hlt
      push Not at hlt
      have e1 : (c ^ 2 * Λ) ^ 3 < (Y ^ 2) ^ 3 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      have e2 : (Y ^ 2) ^ 3 ≤ Λ ^ 2 := by
        calc (Y ^ 2) ^ 3 = (Y ^ 3) ^ 2 := by ring
          _ ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) hY3 2
      have e3 : Λ ^ 2 ≤ (c ^ 2 * Λ) ^ 3 := by
        calc Λ ^ 2 = 1 * Λ ^ 2 := (one_mul _).symm
          _ ≤ (c ^ 6 * Λ) * Λ ^ 2 := by gcongr
          _ = (c ^ 2 * Λ) ^ 3 := by ring
      linarith
    calc Y = √(Y ^ 2) := (Real.sqrt_sq hY0.le).symm
      _ ≤ √(c ^ 2 * Λ) := Real.sqrt_le_sqrt key
      _ = c * √Λ := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  obtain ⟨T, hT⟩ := H Dg (by have := hA.d_mod; omega) hA.hundred_le_d Λ hΛ0 hYc
  have hex : ∃ T : ℕ, T.Prime ∧ Dg.ArithT T ∧ Λ < Real.log T ∧ Real.log T ≤ Λ + Real.log 2 := ⟨T, hT⟩
  have hA0 : 0 ≤ ∑ s ∈ Dg.TT, Dg.a s := Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le
  refine ⟨le_rfl, ?_, fun _ => ?_⟩
  · show (∑ s ∈ Dg.TT, Dg.a s) * 0 ≤ _
    rw [mul_zero]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hA.big.pos.le _) hA0) (by norm_num)
  · show (sharpT Dg u).Prime ∧ Dg.ArithT (sharpT Dg u) ∧ Λ - 0 ≤ Real.log (sharpT Dg u)
    rw [sharpT, dite_eq_left hex, sub_zero]
    exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2.1.le⟩

/-! ## (F) + (V) -/

/-- **The places over `T`**: for places all containing `T ≠ 0`, `|ST|·log 2 ≤ Σ_{P∈ST} log N(P) ≤ [K:ℚ]·log T`. Each
`N(P) ≥ 2`; distinct places are coprime, so `∏_{P∈ST} P ∣ T·O_K` (`Finset.prod_dvd_of_coprime`), and
`N(T·O_K) = T^{[K:ℚ]}` (`Ideal.absNorm_span_natCast`). -/
theorem sum_log_absNorm_le {K : Type*} [Field K] [NumberField K] {ST : Finset (HeightOneSpectrum (𝓞 K))} {T : ℕ}
    (hT : T ≠ 0) (h : ∀ P ∈ ST, (T : 𝓞 K) ∈ P.asIdeal) :
    ST.card * Real.log 2 ≤ ∑ P ∈ ST, Real.log (Ideal.absNorm P.asIdeal : ℝ) ∧
      ∑ P ∈ ST, Real.log (Ideal.absNorm P.asIdeal : ℝ) ≤ Module.finrank ℚ K * Real.log T := by
  have h2 (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal := by
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    omega
  constructor
  · rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun P _ => Real.log_le_log (by norm_num) (by exact_mod_cast h2 P)
  have hdvd : ∏ P ∈ ST, P.asIdeal ∣ Ideal.span {(T : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P hP =>
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 (h P hP))
    have := P.isMaximal
    have := Q.isMaximal
    exact Ideal.isCoprime_of_isMaximal fun he => hPQ (HeightOneSpectrum.ext he)
  have hle : ∏ P ∈ ST, Ideal.absNorm P.asIdeal ≤ T ^ Module.finrank ℚ K := by
    have := map_dvd Ideal.absNorm hdvd
    rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
    exact Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hT) _) this
  have hne (P : HeightOneSpectrum (𝓞 K)) : (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (by have := h2 P; omega)
  rw [← Real.log_prod fun P _ => hne P, ← Real.log_pow]
  exact Real.log_le_log (Finset.prod_pos fun P _ => (Nat.cast_pos.2 (by have := h2 P; omega)))
    (by exact_mod_cast hle)

/-- **The auxiliary prime is prime**: the least prime of its window, or `2`. -/
theorem sharpT_prime (Dg : SharpDesign S κ x ε X) (u : S.A) : (sharpT Dg u).Prime := by
  classical
  unfold sharpT
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact Nat.prime_two

/-- **`log T ≤ x`** for the auxiliary prime: `log T ≤ Λ_u + log 2 ≤ x` (`Adm.lam_add_log_two_le`), or `T = 2`. -/
theorem log_sharpT_le {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm) (u : S.A) : Real.log (sharpT Dg u) ≤ x := by
  classical
  unfold sharpT
  split_ifs with h
  · exact (Nat.find_spec h).2.2.2.trans (hA.lam_add_log_two_le u)
  · rw [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, hA.big.x_ge]

/-- **The budget of (F)**: the exact constant of the base word is at most `x^{4ε}Σ_t a_t/8`. With `A = Σ_t a_t`,
`3|ν| log k ≤ 36A log x ≤ 0.036x^εA`, `2(Σλ)⁺ Σ_{P∈ST} log N(P)/(k[E:ℚ]) ≤ 4A·log T/k ≤ 4A` and
`|ST| log 2 ≤ [E:ℚ] log T ≤ A`, and `5A ≤ x^εA/1000`. -/
theorem cFx_le {Dg : SharpDesign S κ x ε X} (hA : Dg.Adm) (u : S.A) :
    HermForms.cFx Dg.R.k (sharpLam0 Dg u) (sharpST Dg u) ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8 := by
  unfold HermForms.cFx
  set A := ∑ s ∈ Dg.TT, Dg.a s
  set L := ∑ P ∈ sharpST Dg u, Real.log (Ideal.absNorm P.asIdeal : ℝ)
  have hx0 := hA.big.pos
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le
  -- the weights
  have hp : Dg.PinnedTo u (Dg.hc u) := fun _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  have hk0 : Dg.R.k = Dg.R.k + 0 * (Dg.R.t + 1) := by rw [zero_mul, add_zero]
  have hν : ((∑ ρ, ∑ i, WeylFock.natW (sharpLam0 Dg u ρ) i : ℕ) : ℝ) ≤ 2 * A := hA.sum_natW_le hp hk0
  have hlam : max 0 (∑ ρ, ∑ i, (sharpLam0 Dg u ρ i : ℝ)) ≤ 2 * A := hA.sum_wt0_le hp hk0
  -- the ranks
  have hlk := hA.log_k_le
  have hlx := hA.log_le
  have hk1 : (1 : ℝ) ≤ Dg.R.k := by rw [hA.k_eq]; exact hA.big.designK_le.1
  have hlk0 : 0 ≤ Real.log Dg.R.k := Real.log_nonneg hk1
  have hxk : x ≤ Dg.R.k := by
    rw [hA.k_eq]
    refine le_trans ?_ (designK_mem hA.big).1
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (9 / 2 + 10 * ε) := Real.rpow_le_rpow_of_exponent_le hA.big.one_lt.le (by linarith [hA.big.ε_pos])
  have hxe : 4096 ≤ x ^ ε := hA.big.le_rpow (by linarith [hA.big.ε_pos])
  have hx4 : x ^ ε ≤ x ^ (4 * ε) := Real.rpow_le_rpow_of_exponent_le hA.big.one_lt.le (by linarith [hA.big.ε_pos])
  -- the places of `ST`
  obtain ⟨hcard, hsum⟩ := sum_log_absNorm_le (ST := sharpST Dg u) (sharpT_prime Dg u).ne_zero fun P hP =>
    natCast_mem_of_conj_normPi_mem (mem_of_mem_placesOf hP)
  have hn0 : (0 : ℝ) < Module.finrank ℚ S.E := Nat.cast_pos.2 Module.finrank_pos
  have hnx : (Module.finrank ℚ S.E : ℝ) * x ≤ A := (le_div_iff₀ hx0).1 hA.card_E_le
  have hT := log_sharpT_le hA u
  have hLx : L ≤ Module.finrank ℚ S.E * x := hsum.trans (mul_le_mul_of_nonneg_left hT hn0.le)
  have hL0 : 0 ≤ L := le_trans (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)) hcard
  -- the three terms
  have t1 : ((∑ ρ, ∑ i, WeylFock.natW (sharpLam0 Dg u ρ) i : ℕ) : ℝ) * Real.log Dg.R.k ≤
      2 * A * (6 * Real.log x) := mul_le_mul hν hlk hlk0 (by positivity)
  have t1' : A * Real.log x ≤ A * (x ^ ε / 1000) := mul_le_mul_of_nonneg_left hlx hA0
  have t2 : 2 * max 0 (∑ ρ, ∑ i, (sharpLam0 Dg u ρ i : ℝ)) * L / (Dg.R.k * Module.finrank ℚ S.E) ≤ 4 * A := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul hlam (hLx.trans (mul_le_mul_of_nonneg_left hxk hn0.le)) hL0 (by positivity)
    linarith
  have t5 : A * 4096 ≤ A * x ^ ε := mul_le_mul_of_nonneg_left hxe hA0
  have t6 : A * x ^ ε ≤ A * x ^ (4 * ε) := mul_le_mul_of_nonneg_left hx4 hA0
  linarith

/-- **(F) + (V) for the construction** (`SharpPieces.slopeFV` at `adm := Adm`, `cons := sharpCons`), at every
admissible design: `SharpObj.slopeFV_exact`, with the places of `SG` over `g₀` and `g₁` (`exists_sharpSG`),
`X_c = ⊤`, antitone step-0 weights (`Setting.Ranks.wt0_antitone`) and the budget `cFx_le`. -/
theorem sharpSlopeFV : EventuallyAdm (fun Dg => Dg.Adm)
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((sharpCons Dg).obj u).SlopeFV := by
  refine ⟨1, one_pos, fun ε _ _ => ⟨0, fun Dg _ hA u _ => ?_⟩⟩
  obtain ⟨h₀, h₁⟩ := exists_sharpSG hA
  have hA0 : 0 ≤ ∑ s ∈ Dg.TT, Dg.a s := Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le
  exact (sharpObj Dg u).slopeFV_exact h₀ h₁ (fun _ => rfl) (fun _ => Setting.Ranks.wt0_antitone _ _)
    (div_nonneg (mul_nonneg (Real.rpow_nonneg hA.big.pos.le _) hA0) (by norm_num)) (fun _ => cFx_le hA u) le_rfl

end ZetaBalance
