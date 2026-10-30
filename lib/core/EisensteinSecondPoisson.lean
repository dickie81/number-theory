import EisensteinFirstTransfer

/-! # The companion paper's Lemma 7.2, the second Poisson summation

The companion paper: "The second Poisson summation turns the Möbius
coefficients back into cubic Gauss-sum coefficients." Its Lemma 7.2 is an identity for
`𝓜 = Σ_y Φ(N(y)/Y)|P(y)|²`, the inner sum of `𝒬`. Its proof expands the square, applies
Poisson summation in `y`, turns the Gauss sums around and inserts Möbius for `(z_1, z_2) = 1`
through `w`. This is the direction of `pair_char_form` (Möbius columns to Gauss-sum columns), with the
columns twisted by `ξ₁(n)χ_n(c)`, `c = C⁴d·t⁶`, and complex test functions.

Lemma 7.2 is stated for the characters modulo any `m` with `4 ∣ m`. The
expansions need unit classes (`pairTerm_expandTw`, `pair_char_formTw`, `alphaQ_pair`), a Möbius
column through a set with a non-unit class vanishes (`alphaQ_eq_zero`), and the zero frequency of
`Mq_rowcol` runs over the sets with a unit class modulo `m` (`sum_sum_filter_eq`).

* **The twisted paired factor** (`pairTerm_expandTw`) and **the split** (`pair_char_formTw`).
* **The expansion** (`conj_Pcol`, `Mq_expand`, `alphaQ_pair`).
* **The column factorization** (`UU_kapC`, `rcQ`, `term_factorQ`) and **the chain** (`xi_chainQ`).
* **`Mq_rowcol`**: `𝓜` in row/column form; **`zero_Mq_le`**: its zero frequency.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

variable {m : 𝓞 K}

/-! ### The conjugated column sum and its expansion -/

/-- The coefficient `conj(μ(M)ξ₁(M)χ_M(c)·U(N(M)/ℓ))` of the conjugated column sum. -/
def alphaQ (ξ1 : MulChar (𝓞 K ⧸ span {m}) ℂ) (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K)
    (M : Finset Pr) : ℂ :=
  conj ((-1 : ℂ) ^ M.card * ξ1 (cls m M) * chiS M c * U (nI M / ℓ))

theorem conj_Pcol (ξ1 : MulChar (𝓞 K ⧸ span {m}) ℂ) (U : ℝ → ℂ) (β L : ℝ)
    (b T V : Finset Pr) (y : 𝓞 K) :
    conj (Pcol ξ1 U β L b T V y) = ∑ M ∈ fsLe (2 * β * ellS L b T V),
      alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * chiS M y := by
  unfold Pcol
  rw [map_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  unfold alphaQ colP
  simp only [map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  ring

/-- **The expansion of the second mean square** (the companion paper's "Expand the square"):
`𝓜 = Σ_y Φ(N(y)/Y)|P(y)|²` is `Σ_{A₁,A₂} α(A₁)ᾱ(A₂)·Σ_u χ_{A₁}(u)χ̄_{A₂}(u)·Φ(u/√Y)` with `α = alphaQ`. -/
theorem Mq_expand (ξ1 : MulChar (𝓞 K ⧸ span {m}) ℂ) (U : ℝ → ℂ) (β L : ℝ)
    (b T V : Finset Pr) {Y : ℝ} (hY : 0 < Y) :
    ∑' y : 𝓞 K, Pcol ξ1 U β L b T V y * conj (Pcol ξ1 U β L b T V y) *
        Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) =
      ∑ A1 ∈ fsLe (2 * β * ellS L b T V), ∑ A2 ∈ fsLe (2 * β * ellS L b T V),
        alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) A1 *
          conj (alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) A2) *
          ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt Y : ℂ)) := by
  have hQ : ∀ y : 𝓞 K, Pcol ξ1 U β L b T V y * conj (Pcol ξ1 U β L b T V y) *
      Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) =
      (∑ M ∈ fsLe (2 * β * ellS L b T V),
          alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * chiS M y) *
        conj (∑ M ∈ fsLe (2 * β * ellS L b T V),
          alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * chiS M y) *
        Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) := fun y => by
    rw [← conj_Pcol, Complex.conj_conj]; ring
  rw [tsum_congr hQ]
  exact majorant_expand Y hY _ _

/-- The weight of a pair of twisted Möbius columns, apart from the characters modulo `m` and the
signs: `χ̄_{A₁}(c)χ_{A₂}(c)·Ū(N(A₁)/ℓ)U(N(A₂)/ℓ)`. -/
def wQ (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K) (A1 A2 : Finset Pr) : ℂ :=
  conj (chiS A1 c) * chiS A2 c * (conj (U (nI A1 / ℓ)) * U (nI A2 / ℓ))

/-- **The coefficient of a pair of twisted Möbius columns**: `α(A₁)ᾱ(A₂)` is the weight `wQ` times
the signs and `ξ̄₁(A₁∖A₂)ξ₁(A₂∖A₁)` (the characters at `A₁∩A₂` cancel). -/
theorem alphaQ_pair [NeZero m] (ξ1 : MulChar (𝓞 K ⧸ span {m}) ℂ) (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K)
    (A1 A2 : Finset Pr) (hB : IsUnit (cls m (A1 ∩ A2))) :
    alphaQ ξ1 U ℓ c A1 * conj (alphaQ ξ1 U ℓ c A2) =
      wQ U ℓ c A1 A2 * (conj (ξ1 (cls m (A1 \ A2))) * ξ1 (cls m (A2 \ A1)) *
        ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card)) := by
  have hd1 : Disjoint (A1 ∩ A2) (A1 \ A2) := (Finset.disjoint_sdiff_inter A1 A2).symm
  have hd2 : Disjoint (A1 ∩ A2) (A2 \ A1) := by
    rw [Finset.inter_comm]; exact (Finset.disjoint_sdiff_inter A2 A1).symm
  have e1 : A1 = (A1 ∩ A2) ∪ (A1 \ A2) := by rw [Finset.union_comm, Finset.sdiff_union_inter]
  have e2 : A2 = (A1 ∩ A2) ∪ (A2 \ A1) := by
    rw [Finset.inter_comm, Finset.union_comm, Finset.sdiff_union_inter]
  have k1 : ξ1 (cls m A1) = ξ1 (cls m (A1 ∩ A2)) * ξ1 (cls m (A1 \ A2)) := by
    conv_lhs => rw [e1]
    rw [cls_union hd1, map_mul]
  have k2 : ξ1 (cls m A2) = ξ1 (cls m (A1 ∩ A2)) * ξ1 (cls m (A2 \ A1)) := by
    conv_lhs => rw [e2]
    rw [cls_union hd2, map_mul]
  have hB : ξ1 (cls m (A1 ∩ A2)) * conj (ξ1 (cls m (A1 ∩ A2))) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_xi_cls ξ1 hB]; simp
  unfold alphaQ wQ
  simp only [map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  rw [k1, k2]
  simp only [map_mul]
  linear_combination ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card * conj (ξ1 (cls m (A1 \ A2))) *
    ξ1 (cls m (A2 \ A1)) * conj (chiS A1 c) * chiS A2 c * conj (U (nI A1 / ℓ)) *
    U (nI A2 / ℓ)) * hB

/-- **The weights after the change of variables, conjugate on the first column**:
`Ū(N(bTVm₁)/ℓ)·U(N(bTVm₂)/ℓ)·2H/(√3·√(N(Vm₁)N(Vm₂))·N(T)) = 2H·N(b)/(√3·ℓ)·Ū₀(…m₁…)·U₀(…m₂…)`. -/
theorem UU_kapC (U : ℝ → ℂ) {ℓ H nb nT nV n1 n2 : ℝ} (hℓ : 0 < ℓ) (hb : 0 < nb) (hT : 0 < nT)
    (hV : 0 < nV) (h1 : 0 < n1) (h2 : 0 < n2) :
    conj (U (nb * nT * (nV * n1) / ℓ)) * U (nb * nT * (nV * n2) / ℓ) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ) =
      ((2 * H * nb / (Real.sqrt 3 * ℓ) : ℝ) : ℂ) *
        (conj (MellinSep.W0c U (nb * nT * nV * n1 / ℓ)) * MellinSep.W0c U (nb * nT * nV * n2 / ℓ)) := by
  have h := WW_kapC U (H := H) hℓ hb hT hV h2 h1
  rw [show nV * n2 * (nV * n1) = nV * n1 * (nV * n2) by ring] at h
  calc conj (U (nb * nT * (nV * n1) / ℓ)) * U (nb * nT * (nV * n2) / ℓ) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ)
      = U (nb * nT * (nV * n2) / ℓ) * conj (U (nb * nT * (nV * n1) / ℓ)) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ) := by ring
    _ = _ := by rw [h]; ring

/-- The term of the second dual sum at `(b, T, V, μ, M₁, M₂)` (the companion paper's `g = b ∪ T`,
`e = T`, `w = V`, `h = μ` and `n_i = M_i` in its proof of Lemma 7.2): the sign, the row factor
`ā_{ξ_a}(V)a_{ξ_b}(V)|χ_V(μ)|²` with the twist `|χ_{bT}(c)|²|χ_V(c)|²`, the normalization
`2H·N(b)/(√3·ℓ)`, the two columns `colA·χ(c)`, the weights `U₀` and the dual weight. -/
def rcQ (U : ℝ → ℂ) (ℓ H : ℝ) (c : 𝓞 K) (ξa ξb : MulChar (𝓞 K ⧸ span {m}) ℂ)
    (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr) : ℂ :=
  ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
    (conj (aXi ξa (idl V)) * aXi ξb (idl V) * (chiS V μ * conj (chiS V μ)) *
      ((conj (chiS (b ∪ T) c) * chiS (b ∪ T) c) * (conj (chiS V c) * chiS V c))) *
    ((2 * H * nI b / (Real.sqrt 3 * ℓ) : ℝ) : ℂ) *
    (conj (colA ξa (eS T * μ) (eS T * eS V) M1 * chiS M1 c) *
      (colA ξb (eS T * μ) (eS T * eS V) M2 * chiS M2 c)) *
    (conj (MellinSep.W0c U (nI b * nI T * nI V * nI M1 / ℓ)) *
      MellinSep.W0c U (nI b * nI T * nI V * nI M2 / ℓ)) *
    dualW H (V ∪ M1) (V ∪ M2) T μ

/-- **One term of the second Möbius-expanded sum in row/column form** (`term_factor`
with complex weights and the twist `χ̄_{A₁}(c)χ_{A₂}(c)`). -/
theorem term_factorQ (U : ℝ → ℂ) {ℓ H : ℝ} (hℓ : 0 < ℓ) (c : 𝓞 K)
    (ξa ξb : MulChar (𝓞 K ⧸ span {m}) ℂ) (E : Finset (𝓞 K)) {b T V M1 M2 : Finset Pr}
    (hbT : Disjoint b T) (hbV : Disjoint b V) (hb1 : Disjoint b M1) (hb2 : Disjoint b M2)
    (hTV : Disjoint T V) (hT1 : Disjoint T M1) (hT2 : Disjoint T M2) (hV1 : Disjoint V M1)
    (hV2 : Disjoint V M2) :
    (-1 : ℂ) ^ V.card * (wQ U ℓ c ((b ∪ T) ∪ (V ∪ M1)) ((b ∪ T) ∪ (V ∪ M2)) *
        tauXi H E ξa ξb (V ∪ M1) (V ∪ M2) T) =
      ∑ μ ∈ E, rcQ U ℓ H c ξa ξb b T V μ M1 M2 := by
  have hd1 : Disjoint (b ∪ T) (V ∪ M1) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb1⟩, hTV, hT1⟩
  have hd2 : Disjoint (b ∪ T) (V ∪ M2) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb2⟩, hTV, hT2⟩
  have hn1 : nI ((b ∪ T) ∪ (V ∪ M1)) = nI b * nI T * (nI V * nI M1) := by
    rw [nI_union hd1, nI_union hbT, nI_union hV1]
  have hn2 : nI ((b ∪ T) ∪ (V ∪ M2)) = nI b * nI T * (nI V * nI M2) := by
    rw [nI_union hd2, nI_union hbT, nI_union hV2]
  have hk : kap H (V ∪ M1) (V ∪ M2) T =
      2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) := by
    unfold kap; rw [nI_union hV1, nI_union hV2]
  have hUK : conj (U (nI ((b ∪ T) ∪ (V ∪ M1)) / ℓ)) * U (nI ((b ∪ T) ∪ (V ∪ M2)) / ℓ) *
      ((kap H (V ∪ M1) (V ∪ M2) T : ℝ) : ℂ) =
      ((2 * H * nI b / (Real.sqrt 3 * ℓ) : ℝ) : ℂ) *
        (conj (MellinSep.W0c U (nI b * nI T * nI V * nI M1 / ℓ)) *
          MellinSep.W0c U (nI b * nI T * nI V * nI M2 / ℓ)) := by
    rw [hn1, hn2, hk]
    exact UU_kapC U hℓ (nI_pos b) (nI_pos T) (nI_pos V) (nI_pos M1) (nI_pos M2)
  unfold tauXi
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hcf := col_factor ξa ξb hTV.symm hT1.symm hT2.symm hV1 hV2 μ
  unfold wQ rcQ
  rw [chiS_union hd1 c, chiS_union hd2 c, chiS_union hV1 c, chiS_union hV2 c]
  calc _ = ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
        ((conj (chiS (b ∪ T) c) * chiS (b ∪ T) c) * (conj (chiS V c) * chiS V c)) *
        (conj (U (nI ((b ∪ T) ∪ (V ∪ M1)) / ℓ)) * U (nI ((b ∪ T) ∪ (V ∪ M2)) / ℓ) *
          ((kap H (V ∪ M1) (V ∪ M2) T : ℝ) : ℂ)) *
        (conj (aXi ξa (idl (V ∪ M1))) * aXi ξb (idl (V ∪ M2)) *
          (chiS (V ∪ M1) (eS T) * conj (chiS (V ∪ M2) (eS T))) *
          conj (chiS (V ∪ M1) μ * conj (chiS (V ∪ M2) μ))) *
        (conj (chiS M1 c) * chiS M2 c) * dualW H (V ∪ M1) (V ∪ M2) T μ := by
        simp only [map_mul]; ring
    _ = _ := by rw [hUK, hcf]; simp only [map_mul]; ring

/-- **The chain for one pair of characters, second direction** (`xi_chain` with the
weight `wQ`): `sum_pair_chain` with the factorization `term_factorQ`. -/
theorem xi_chainQ (U : ℝ → ℂ) {ℓ H : ℝ} (hℓ : 0 < ℓ) (c : 𝓞 K) (E : Finset (𝓞 K))
    (ξa ξb : MulChar (𝓞 K ⧸ span {m}) ℂ) (U0 : Finset Pr) (𝒜 : Finset (Finset Pr))
    (h𝒜 : ∀ A ∈ 𝒜, A ⊆ U0) (hvan : ∀ A ⊆ U0, A ∉ 𝒜 → U (nI A / ℓ) = 0) :
    ∑ A1 ∈ 𝒜, ∑ A2 ∈ 𝒜, wQ U ℓ c A1 A2 *
        ∑ T ∈ (A1 ∩ A2).powerset, tauXi H E ξa ξb (A1 \ A2) (A2 \ A1) T =
      ∑ b ∈ U0.powerset, ∑ T ∈ (U0 \ b).powerset, ∑ V ∈ (U0 \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U0 \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U0 \ (b ∪ T)) \ V).powerset,
          rcQ U ℓ H c ξa ξb b T V μ M1 M2 := by
  rw [sum_family_eq_powerset U0 𝒜 h𝒜 _ (fun A1 h1 A2 h2 h => by
    rcases h with h | h
    · unfold wQ; rw [hvan A1 h1 h]; simp
    · unfold wQ; rw [hvan A2 h2 h]; simp)]
  exact sum_pair_chain U0 (wQ U ℓ c) (fun B C1 C2 => wQ U ℓ c (B ∪ C1) (B ∪ C2)) (fun _ _ _ => rfl)
    (tauXi H E ξa ξb) E (rcQ U ℓ H c ξa ξb)
    (fun hbT hbV hb1 hb2 hTV hT1 hT2 hV1 hV2 =>
      term_factorQ U hℓ c ξa ξb E hbT hbV hb1 hb2 hTV hT1 hT2 hV1 hV2)

/-- A double sum over `s × s` whose terms vanish when either index fails `p` is the double sum over
`s.filter p`. -/
theorem sum_sum_filter_eq {ι : Type*} {s : Finset ι} {p : ι → Prop} [DecidablePred p]
    {g : ι → ι → ℂ} (h1 : ∀ x y, ¬p x → g x y = 0) (h2 : ∀ x y, ¬p y → g x y = 0) :
    ∑ x ∈ s, ∑ y ∈ s, g x y = ∑ x ∈ s.filter p, ∑ y ∈ s.filter p, g x y := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with hy
    · rfl
    · exact h2 x y hy
  · exact Finset.sum_eq_zero fun y _ => h1 x y hx

theorem alphaQ_eq_zero (ξ1 : MulChar (𝓞 K ⧸ span {m}) ℂ) (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K)
    {M : Finset Pr} (hM : ¬IsUnit (cls m M)) : alphaQ ξ1 U ℓ c M = 0 := by
  unfold alphaQ; rw [MulChar.map_nonunit ξ1 hM]; simp

/-- **The zero frequency of the second mean square** (the companion paper's "`|Z|≪_{I_*,Φ}Yℓ‖U‖_∞^2`"
of its Lemma 7.2): with `|U| ≤ N_U`, the zero frequency of `Mq_rowcol` over a family `𝒜` has norm at
most `#𝒜·N_U²·2Y/√3·|Φ̂(0)|`; for `𝒜 = fsLe (2βℓ)`, `#𝒜 ≤ (2κ+5)·max(2βℓ, 1)` (`card_fsLe_le_max`). -/
theorem zero_Mq_le {U : ℝ → ℂ} {NU : ℝ} (hNU : ∀ x, ‖U x‖ ≤ NU) (ℓ : ℝ) (c : 𝓞 K) {Y : ℝ}
    (hY : 0 ≤ Y) (𝒜 : Finset (Finset Pr)) :
    ‖∑ A ∈ 𝒜, wQ U ℓ c A A *
        ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap Y ∅ ∅ T : ℂ) * dualG 0‖ ≤
      𝒜.card * (NU ^ 2 * (2 * Y / Real.sqrt 3 * ‖dualG 0‖)) := by
  have hNU0 : 0 ≤ NU := (norm_nonneg _).trans (hNU 0)
  refine norm_zeroSum_le hY 𝒜 _ fun A _ => ?_
  unfold wQ
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, sq]
  have := norm_chiS_le A c
  calc ‖chiS A c‖ * ‖chiS A c‖ * (‖U (nI A / ℓ)‖ * ‖U (nI A / ℓ)‖) ≤ 1 * 1 * (NU * NU) := by
        gcongr <;> first | exact this | exact hNU _
    _ = NU * NU := by ring

end Eis

end

#print axioms Eis.conj_Pcol
#print axioms Eis.Mq_expand
#print axioms Eis.alphaQ_pair
#print axioms Eis.UU_kapC
#print axioms Eis.term_factorQ
#print axioms Eis.xi_chainQ
#print axioms Eis.sum_sum_filter_eq
#print axioms Eis.alphaQ_eq_zero
#print axioms Eis.zero_Mq_le
