import SourceKeys

/-!
# The realisation core of the second local theorem: key presentations, conversion, iteration (L6 N8, C4)

The abstract realisation at the main edge (`g = 1`) of N8: a polynomial `T = Z·fixFactor(c) + p^c·Y` with `Z` a sum
of key-presentable polynomials is *realisable* at level `o` with margin `c` (`RealAt`): there is an integral `F` of
the same multidegree with `Φ_1 F ≡ ϖ^o·T (mod ϖ^{o+c})` and `ord_{g′} F ≥ o + c` at every `g′` off the main plane.

**Conventions** (those of `SourceKeys`). `Φ_g = ad … g`; `ord_g F ≥ i` is `OrdGe ϖ i (Φ_g F)`. A *key* of level `o`
is `IsPlaneKey` (integral, on the tops, leading form `κ₀` homogeneous of `ϖ`-degree `o` and of order `o`, error of
order `o + 1` at `g = 1`, `ord_{g′}κ ≥ o` at every `g′`); `KeyT` packs `(κ, κ₀, o)`. *Unscaled* polynomials are
integral, on the tops and of `ϖ`-degree `0`, hence fixed by `Φ_1` (`ad_one_of_nd`).

**Key presentations** (N8's). `IsKeyMono A o`: `A` is a product of leading forms of keys whose levels sum to `o`;
`keyGens o` the products `A·h`, `h` unscaled; `KeyPres o P`: every monomial of `P` has `ϖ`-degree `o` and `ϖ^o·P` is a
sum of generators of level `o`; `keyPresSpan` the sums of key-presentable polynomials, closed under products
(`keyPresSpan_mul`), containing the unscaled polynomials (`keyPres_unscaled`).

**Terms.** A term is `(i, keys, a, μ, h)` with symbol `ϖ^i·∏κ⁰_l·Ξ⁰^a·budgetProd^μ·h` (`symT`), raw lift
`ϖ^i·∏κ_l·Ξ_loc^a·budgetProd^μ·h` (`rawT`) and level `i + Σ_l o_l` (`levT`); it is *valid* for the precision `t`
(`ValidT`) when the keys are keys, `h` is unscaled, `a ≥ t − lev` and `μ ≥ (2Q + 1)(t − lev)`. `realSub t` is the
additive group of polynomials `P ≡ Φ_1 G (mod ϖ^t)` with `G` integral and `ord_{g′} G ≥ t` off the plane.

**Main results.**
* *Conversion* (`monomial_conversion`): `ϖ^{nd m}·X^m·budgetProd^ν` (`m` on the tops, `piDeg m ≤ ν` at every letter)
  is a sum of generators of level `nd m`: each scaled variable is paired with the `Tp` of its late letter, giving the
  leading form of an even key or, through the odd cofactor identity, a sum of odd-key leading forms (`scaled_var_mem`).
* *Iteration* (`iterate`): the abstract lemma, raw lifts small off the plane whose `Φ_1`-errors are higher-level
  symbols realise every symbol.
* *The core* (`realise_core`).

**The route.** `valid_mem`: every valid term is in `realSub t`, by downward induction on the level. For a valid term
below `t`, `Φ_1(raw)` is in `realSub t`, and `Φ_1(raw) − sym` is (`step_mem`) a sum of *pre-terms*
`ϖ^i·∏_{l∈U}κ⁰_l·Ξ⁰^{a′}·budgetProd^μ·h′·P` of base level `lev`: with `R = Φ_1Ξ_loc − Ξ⁰` (graded-integral, of order
`1`, `locErr`) and `(R + Ξ⁰)^a` expanded binomially, and `∏Φ_1κ_l − ∏κ⁰_l` expanded over the untouched sublists `U`
(`keys_expand`: `P` graded-integral of order `d + s`, `s ≥ 1` touched keys of total level `d ≤ 2Qs`; a list recursion,
no subsets). A pre-term is converted monomial by monomial (`preterm_mem`): a monomial `c_mX^m` of `P` with
`v(c_m) = v ≥ max(nd m, d + s)` either has new level `≥ t` or becomes, by conversion, a sum of symbols of valid terms
of level `lev − d + v > lev`; the budget consumed is `nd m ≤ v ≤ (v − d) + 2Qs ≤ (2Q + 1)(v − d)`, the localiser
exponent drops by at most the level gain. Finally the initial terms `A·Ξ⁰^c·budgetProd^{(2Q+3)c}·h` of `ϖ^o·Z` are
valid for `t = o + c`, `ϖ^o·p^c·Y` has order `o + 2c`, and a multidegree component is taken (`ad_comp`).

**Readings of the planning statements.** `IsPlaneKey` carries the extra field `lead_tops` (the leading form lives on
the tops; needed to convert error monomials). `iterate` is stated as in the spec, but `realise_core` runs the
iteration through `realSub` directly, so that coinciding terms need no bookkeeping. The spec's expansion over subsets
`(S, i′)` is replaced by the list recursion of `keys_expand`, with the same budget arithmetic.
-/

namespace SourceCore

open MvPolynomial Finset LetterFock LocalOrbit SymbolData InertModel SourceKeys

open scoped Matrix

noncomputable section

variable {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O} {p n' r K : ℕ}

/-! ## Realisability, key products and key presentations -/

section Defs

variable (ϖ) in
/-- **Realised at level `o` with margin `c`** (main edge): an integral `F` of the same multidegree with
`Φ_1 F ≡ ϖ^o·σ₀ (mod ϖ^{o+c})` and `ord_{g′} F ≥ o + c` at every `g′` off the main plane. -/
def RealAt (p c o : ℕ) (σ₀ : LPol (Fin n') (r + K) Kf) : Prop :=
  ∃ F : LPol (Fin n') (r + K) Kf, OrdGe ϖ 0 F ∧ (∀ d, σ₀ ∈ LHom Kf d → F ∈ LHom Kf d) ∧
    OrdGe ϖ (o + c) (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) F - (algebraMap O Kf ϖ ^ o) • σ₀) ∧
    ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, OffPlane p g' → OrdGe ϖ (o + c) (ad ι σ ϖ n' r K g' F)

variable (W ι σ ϖ) in
/-- **A key product of level `o`**: a product of leading forms of keys whose levels sum to `o`. -/
def IsKeyMono (TT : Finset (Fin n')) (Q : ℕ) (A : LPol (Fin n') (r + K) Kf) (o : ℕ) : Prop :=
  ∃ l : List (LPol (Fin n') (r + K) Kf × LPol (Fin n') (r + K) Kf × ℕ),
    (∀ y ∈ l, IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2) ∧ A = (l.map fun y => y.2.1).prod ∧
      o = (l.map fun y => y.2.2).sum

variable (W ι σ ϖ) in
/-- **The generators of level `o`**: key products of level `o` times unscaled polynomials. -/
def keyGens (TT : Finset (Fin n')) (Q o : ℕ) : Set (LPol (Fin n') (r + K) Kf) :=
  {z | ∃ A h, IsKeyMono W ι σ ϖ TT Q A o ∧ Unscaled ϖ TT h ∧ z = A * h}

variable (W ι σ ϖ) in
/-- **Key-presentable of `ϖ`-degree `o`** (N8's key presentation): every monomial of `ϖ`-degree `o`, and `ϖ^o·P` is a
sum of generators of level `o`. -/
def KeyPres (TT : Finset (Fin n')) (Q o : ℕ) (P : LPol (Fin n') (r + K) Kf) : Prop :=
  (∀ m ∈ P.support, nd r (vecF n') m = o) ∧
    (algebraMap O Kf ϖ ^ o) • P ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q o)

variable (W ι σ ϖ) in
/-- **Sums of key-presentable polynomials.** -/
def keyPresSpan (TT : Finset (Fin n')) (Q : ℕ) : AddSubmonoid (LPol (Fin n') (r + K) Kf) :=
  AddSubmonoid.closure {P | ∃ o, KeyPres W ι σ ϖ TT Q o P}

end Defs

/-! ## Unscaled polynomials and `Φ_1` -/

section Unscaled

/-- **Unscaled polynomials multiply.** -/
theorem unscaled_mul {TT : Finset (Fin n')} {h h' : LPol (Fin n') (r + K) Kf} (hh : Unscaled ϖ TT h)
    (hh' : Unscaled ϖ TT h') : Unscaled ϖ TT (h * h') := by
  refine ⟨by simpa using ordGe_mul hh.1 hh'.1, Subalgebra.mul_mem _ hh.2.1 hh'.2.1, ?_⟩
  exact hom_iff.2 (by simpa using (hom_iff.1 hh.2.2).mul (hom_iff.1 hh'.2.2))

/-- **Integral constants are unscaled.** -/
theorem unscaled_C {TT : Finset (Fin n')} (o : O) : Unscaled ϖ TT (C (algebraMap O Kf o) : LPol (Fin n') (r + K) Kf) :=
  ⟨ordGe_C_int o, Subalgebra.algebraMap_mem _ _, hom_iff.2 (isWeightedHomogeneous_C _ _)⟩

/-- **`1` is unscaled.** -/
theorem unscaled_one {TT : Finset (Fin n')} : Unscaled ϖ TT (1 : LPol (Fin n') (r + K) Kf) := by
  simpa using unscaled_C (TT := TT) (ϖ := ϖ) (Kf := Kf) (r := r) (K := K) (1 : O)

/-- **`Φ_1` on a monomial** multiplies it by `ϖ^{nd}`. -/
theorem ad_one_monomial (m : Fin n' × Fin (r + K) →₀ ℕ) (a : Kf) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (monomial m a) =
      monomial m (a * algebraMap O Kf ϖ ^ nd r (vecF n') m) := by
  classical
  rw [monomial_eq, map_mul, algHom_C, Finsupp.prod, map_prod]
  simp only [map_pow, ad_one_X, mul_pow, prod_mul_distrib]
  rw [monomial_eq, Finsupp.prod, ← mul_assoc, C_mul]
  congr 2
  rw [show ∏ v ∈ m.support, C (if scaled r (vecF n') v then algebraMap O Kf ϖ else 1) ^ m v =
      C (∏ v ∈ m.support, (if scaled r (vecF n') v then algebraMap O Kf ϖ else 1) ^ m v) by
    rw [map_prod]; simp only [map_pow]]
  congr 1
  rw [nd, Finsupp.weight_apply, Finsupp.sum, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

/-- **The coefficients of `Φ_1 P`.** -/
theorem coeff_ad_one (P : LPol (Fin n') (r + K) Kf) (m : Fin n' × Fin (r + K) →₀ ℕ) :
    (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) P).coeff m =
      P.coeff m * algebraMap O Kf ϖ ^ nd r (vecF n') m := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [ad_one_monomial, coeff_sum, coeff_monomial]
  rw [sum_eq_single m (fun b _ hb => by simp [hb]) (fun hm => by simp [notMem_support_iff.1 hm])]
  simp

/-- **`Φ_1` fixes unscaled polynomials.** -/
theorem ad_one_of_nd {P : LPol (Fin n') (r + K) Kf} (hP : ∀ m ∈ P.support, nd r (vecF n') m = 0) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) P = P := by
  ext m
  rw [coeff_ad_one]
  by_cases hm : m ∈ P.support
  · rw [hP m hm, pow_zero, mul_one]
  · rw [notMem_support_iff.1 hm, zero_mul]

/-- **`Φ_1` keeps the support.** -/
theorem support_ad_one (P : LPol (Fin n') (r + K) Kf) :
    (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) P).support ⊆ P.support := fun m hm => by
  rw [mem_support_iff, coeff_ad_one] at hm
  exact mem_support_iff.2 (left_ne_zero_of_mul hm)

/-- **Polynomials on the tops**, read through supports. -/
theorem mem_tops_of_support {TT : Finset (Fin n')} {P P' : LPol (Fin n') (r + K) Kf}
    (hP : P ∈ supported Kf {v | v.1 ∈ TT}) (h : P'.support ⊆ P.support) : P' ∈ supported Kf {v | v.1 ∈ TT} := by
  classical
  rw [mem_supported] at hP ⊢
  intro v hv
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
  obtain ⟨d, hd, hvd⟩ := hv
  exact hP (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨d, h hd, hvd⟩))

/-- **`Φ_1` keeps the tops.** -/
theorem ad_one_mem_tops {TT : Finset (Fin n')} {P : LPol (Fin n') (r + K) Kf} (hP : P ∈ supported Kf {v | v.1 ∈ TT}) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) P ∈ supported Kf {v | v.1 ∈ TT} :=
  mem_tops_of_support hP (support_ad_one P)

/-- **Graded-integral polynomials are integral.** -/
theorem ordGe_of_gInt {P : LPol (Fin n') (r + K) Kf} (hP : P ∈ gInt ϖ r (vecF n')) : OrdGe ϖ 0 P := fun m => by
  obtain ⟨c, hc⟩ := hP m
  exact ⟨ϖ ^ nd r (vecF n') m * c, by rw [hc, pow_zero, one_mul]⟩

/-- **Homogeneous polynomials of order their `ϖ`-degree** are graded-integral. -/
theorem gInt_of_hom {P : LPol (Fin n') (r + K) Kf} {o : ℕ} (hhom : ∀ m ∈ P.support, nd r (vecF n') m = o)
    (hP : OrdGe ϖ o P) : P ∈ gInt ϖ r (vecF n') := fun m => by
  by_cases hm : m ∈ P.support
  · rw [hhom m hm]
    exact hP m
  · exact ⟨0, by rw [notMem_support_iff.1 hm, mul_zero, map_zero]⟩

end Unscaled

/-! ## Products of key presentations -/

section KeyPres

/-- **Key products multiply** (append the key lists). -/
theorem isKeyMono_mul {TT : Finset (Fin n')} {Q : ℕ} {A A' : LPol (Fin n') (r + K) Kf} {o o' : ℕ}
    (hA : IsKeyMono W ι σ ϖ TT Q A o) (hA' : IsKeyMono W ι σ ϖ TT Q A' o') :
    IsKeyMono W ι σ ϖ TT Q (A * A') (o + o') := by
  obtain ⟨l, hl, rfl, rfl⟩ := hA
  obtain ⟨l', hl', rfl, rfl⟩ := hA'
  refine ⟨l ++ l', fun y hy => ?_, by simp, by simp⟩
  rcases List.mem_append.1 hy with h | h
  exacts [hl y h, hl' y h]

/-- **Generators multiply.** -/
theorem keyGens_mul {TT : Finset (Fin n')} {Q o o' : ℕ} {z z' : LPol (Fin n') (r + K) Kf}
    (hz : z ∈ keyGens W ι σ ϖ TT Q o) (hz' : z' ∈ keyGens W ι σ ϖ TT Q o') :
    z * z' ∈ keyGens W ι σ ϖ TT Q (o + o') := by
  obtain ⟨A, h, hA, hh, rfl⟩ := hz
  obtain ⟨A', h', hA', hh', rfl⟩ := hz'
  exact ⟨A * A', h * h', isKeyMono_mul hA hA', unscaled_mul hh hh', by ring⟩

/-- **Sums of generators multiply.** -/
theorem closure_keyGens_mul {TT : Finset (Fin n')} {Q o o' : ℕ} {z z' : LPol (Fin n') (r + K) Kf}
    (hz : z ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q o))
    (hz' : z' ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q o')) :
    z * z' ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q (o + o')) := by
  induction hz using AddSubmonoid.closure_induction with
  | mem x hx =>
    induction hz' using AddSubmonoid.closure_induction with
    | mem y hy => exact AddSubmonoid.subset_closure (keyGens_mul hx hy)
    | zero => simp
    | add y y' _ _ h h' => rw [mul_add]; exact AddSubmonoid.add_mem _ h h'
  | zero => simp
  | add x x' _ _ h h' => rw [add_mul]; exact AddSubmonoid.add_mem _ h h'

/-- **Unscaled polynomials are generators of level `0`.** -/
theorem unscaled_mem_keyGens {TT : Finset (Fin n')} {Q : ℕ} {h : LPol (Fin n') (r + K) Kf} (hh : Unscaled ϖ TT h) :
    h ∈ keyGens W ι σ ϖ TT Q 0 :=
  ⟨1, h, ⟨[], by simp, by simp, by simp⟩, hh, by ring⟩

/-- **Unscaled polynomials are key-presentable of degree `0`.** -/
theorem keyPres_unscaled {TT : Finset (Fin n')} {Q : ℕ} {h : LPol (Fin n') (r + K) Kf} (hh : Unscaled ϖ TT h) :
    KeyPres W ι σ ϖ TT Q 0 h :=
  ⟨hh.2.2, by simpa using AddSubmonoid.subset_closure (unscaled_mem_keyGens (W := W) (ι := ι) (σ := σ) (Q := Q) hh)⟩

/-- **Key presentations multiply**, degrees adding. -/
theorem keyPres_mul {TT : Finset (Fin n')} {Q o o' : ℕ} {P P' : LPol (Fin n') (r + K) Kf}
    (hP : KeyPres W ι σ ϖ TT Q o P) (hP' : KeyPres W ι σ ϖ TT Q o' P') : KeyPres W ι σ ϖ TT Q (o + o') (P * P') := by
  refine ⟨hom_iff.2 ((hom_iff.1 hP.1).mul (hom_iff.1 hP'.1)), ?_⟩
  rw [pow_add, ← smul_mul_smul_comm]
  exact closure_keyGens_mul hP.2 hP'.2

/-- **`keyPresSpan` is closed under products** (key products and unscaled factors multiply). -/
theorem keyPresSpan_mul {TT : Finset (Fin n')} {Q : ℕ} {P P' : LPol (Fin n') (r + K) Kf}
    (hP : P ∈ keyPresSpan W ι σ ϖ TT Q) (hP' : P' ∈ keyPresSpan W ι σ ϖ TT Q) :
    P * P' ∈ keyPresSpan W ι σ ϖ TT Q := by
  induction hP using AddSubmonoid.closure_induction with
  | mem x hx =>
    induction hP' using AddSubmonoid.closure_induction with
    | mem y hy =>
      obtain ⟨o, ho⟩ := hx
      obtain ⟨o', ho'⟩ := hy
      exact AddSubmonoid.subset_closure ⟨o + o', keyPres_mul ho ho'⟩
    | zero => simp
    | add y y' _ _ h h' => rw [mul_add]; exact AddSubmonoid.add_mem _ h h'
  | zero => simp
  | add x x' _ _ h h' => rw [add_mul]; exact AddSubmonoid.add_mem _ h h'

/-- **Leading forms of keys are generators.** -/
theorem lead_mem_closure {TT : Finset (Fin n')} {Q : ℕ} {κ κ₀ : LPol (Fin n') (r + K) Kf} {o : ℕ}
    (h : IsPlaneKey W ι σ ϖ TT Q κ κ₀ o) : κ₀ ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q o) :=
  AddSubmonoid.subset_closure ⟨κ₀, 1, ⟨[(κ, κ₀, o)], by simpa using h, by simp, by simp⟩, unscaled_one, by ring⟩

/-- **Powers of level-`1` sums of generators.** -/
theorem pow_mem_closure {TT : Finset (Fin n')} {Q : ℕ} {z : LPol (Fin n') (r + K) Kf}
    (hz : z ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q 1)) (b : ℕ) :
    z ^ b ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q b) := by
  induction b with
  | zero => simpa using AddSubmonoid.subset_closure (unscaled_mem_keyGens (W := W) (ι := ι) (σ := σ) (Q := Q)
      (unscaled_one (TT := TT) (ϖ := ϖ)))
  | succ b ih => rw [pow_succ]; exact closure_keyGens_mul ih hz

end KeyPres

/-! ## The conversion of scaled monomials (N8 C4) -/

section Conversion

variable [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [NeZero n'] [NeZero r]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The adjugate of the `Tp` matrix is unscaled.** -/
theorem adj_unscaled (hn : Even n') {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁)
    {j x : ℤ} (hx : x ∈ F.late TT j) (c l : Fin r) :
    Unscaled ϖ TT ((Matrix.of fun l' c' : Fin r => pent Kf p K (F.rows TT j x l')
      (x - F.rows TT j x l').toNat (Fin.castAdd K c')).adjugate c l) := by
  classical
  rw [Matrix.adjugate_apply]
  refine ⟨ordGe_det fun a b => ?_, det_mem_subalgebra _ fun a b => ?_, hom_iff.2 (isWH_det fun a b => ?_)⟩
  · rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      exacts [ordGe_one, ordGe_zero 0]
    · exact ordGe_pent _ _ _
  · rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      exacts [Subalgebra.one_mem _, Subalgebra.zero_mem _]
    · exact pent_mem_tops (rows_props hF hx a).2.2 _ _
  · rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      exacts [isWeightedHomogeneous_one _ _, isWeightedHomogeneous_zero _ _ _]
    · exact isWH_pent_plane hn (rows_props hF hx a).1 _ _

/-- **A scaled variable times its `Tp`** is a sum of generators of level `1`: the leading form of an even key, or
through the odd cofactor identity. -/
theorem scaled_var_mem (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) {j x : ℤ} (hx : x ∈ F.late TT j)
    {c : Fin (r + K)} (hc : scaled r (vecF n') (posOf n' x, c)) :
    C (algebraMap O Kf ϖ) * X (posOf n' x, c) * Tp F TT Kf p K j x ∈
      AddSubmonoid.closure (keyGens W ι σ ϖ TT Q 1) := by
  by_cases hxe : Even x
  · rw [scaled_even hn hxe] at hc
    have hc' : r ≤ c.val := by simpa using hc
    obtain ⟨b, rfl⟩ : ∃ b : Fin K, c = Fin.natAdd r b := ⟨⟨c.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
    exact lead_mem_closure (keyEven_isKey hU hn hp hF hQ hx hxe b)
  · rw [scaled_odd hn hxe] at hc
    have hc' : c.val < r := by simpa using hc
    obtain ⟨c', rfl⟩ : ∃ c' : Fin r, c = Fin.castAdd K c' := ⟨⟨c.val, hc'⟩, Fin.ext rfl⟩
    rw [odd_cofactor_identity]
    refine AddSubmonoid.sum_mem _ fun l _ => ?_
    have h := closure_keyGens_mul (AddSubmonoid.subset_closure (unscaled_mem_keyGens (W := W) (ι := ι) (σ := σ)
      (Q := Q) (adj_unscaled (ϖ := ϖ) (p := p) (K := K) hn hF hx c' l)))
      (lead_mem_closure (keyOdd_isKey (K := K) hU hn hp hF hQ hx hxe l))
    rwa [zero_add] at h

omit [NeZero n'] [NeZero r] in
/-- **`piDeg` is additive.** -/
theorem piDeg_add {k : ℕ} (m m' : Fin n' × Fin k →₀ ℕ) (s : Fin n') :
    piDeg r (vecF n') (m + m') s = piDeg r (vecF n') m s + piDeg r (vecF n') m' s := by
  simp only [piDeg, Finsupp.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

omit [NeZero n'] [NeZero r] in
/-- **`piDeg` of a single variable.** -/
theorem piDeg_single {k : ℕ} (a : Fin n' × Fin k) (b : ℕ) (s : Fin n') :
    piDeg r (vecF n') (Finsupp.single a b) s = if a.1 = s ∧ scaled r (vecF n') a then b else 0 := by
  classical
  simp only [piDeg]
  by_cases h : a.1 = s ∧ scaled r (vecF n') a = true
  · rw [ite_eq_left h, sum_eq_single a.2]
    · obtain ⟨h1, h2⟩ := h
      subst h1
      simp [h2]
    · intro c _ hc
      have hne : a ≠ (s, c) := fun h' => hc (by rw [h'])
      simp [hne]
    · simp
  · rw [ite_eq_right h]
    refine sum_eq_zero fun c _ => ?_
    split_ifs with h'
    · rw [Finsupp.single_apply, ite_eq_right]
      rintro rfl
      exact h ⟨rfl, h'⟩
    · rfl

/-- **The conversion, generalised**: with one budget exponent per late letter. -/
theorem conv_gen (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) (m : Fin n' × Fin (r + K) →₀ ℕ)
    (hm : ∀ v ∈ m.support, v.1 ∈ TT) :
    ∀ ν : (Σ _ : ℕ, ℤ) → ℕ, (∀ y ∈ (range F.J).sigma (fun j => F.late TT j),
      piDeg r (vecF n') m (posOf n' y.2) ≤ ν y) →
      C (algebraMap O Kf ϖ ^ nd r (vecF n') m) * monomial m (1 : Kf) *
        ∏ y ∈ (range F.J).sigma (fun j => F.late TT j), Tp F TT Kf p K y.1 y.2 ^ ν y ∈
        AddSubmonoid.closure (keyGens W ι σ ϖ TT Q (nd r (vecF n') m)) := by
  classical
  set S := (range F.J).sigma (fun j => F.late TT j) with hS
  have hTpU : ∀ (ν : (Σ _ : ℕ, ℤ) → ℕ), Unscaled ϖ TT (∏ y ∈ S, Tp F TT Kf p K y.1 y.2 ^ ν y) := fun ν => by
    refine ⟨ordGe_prod fun y _ => by simpa using ordGe_pow (ordGe_Tp F y.1 y.2) (ν y),
      Subalgebra.prod_mem _ fun y hy => Subalgebra.pow_mem _ (Tp_mem_tops hF (mem_sigma.1 hy).2) _, hom_iff.2 ?_⟩
    have h := IsWeightedHomogeneous.prod S (fun y => Tp F TT Kf p K y.1 y.2 ^ ν y) (fun _ => 0) fun y hy => by
      simpa using (isWH_Tp hn hF (mem_sigma.1 hy).2).pow (ν y)
    rwa [sum_const_zero] at h
  induction m using Finsupp.induction with
  | zero =>
    intro ν _
    simpa using AddSubmonoid.subset_closure (unscaled_mem_keyGens (W := W) (ι := ι) (σ := σ) (Q := Q) (hTpU ν))
  | single_add a b f haf hb ih =>
    intro ν hν
    have ha : a.1 ∈ TT := hm a (Finsupp.mem_support_iff.2 (by simp [Finsupp.notMem_support_iff.1 haf, hb]))
    have hf : ∀ v ∈ f.support, v.1 ∈ TT := fun v hv => hm v (Finsupp.mem_support_iff.2 (by
      rw [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (by rintro rfl; exact haf hv), zero_add]
      exact Finsupp.mem_support_iff.1 hv))
    have hndm : nd r (vecF n') (Finsupp.single a b + f) =
        (if scaled r (vecF n') a then b else 0) + nd r (vecF n') f := by
      rw [map_add, nd, Finsupp.weight_single]
      split_ifs <;> simp
    rw [monomial_single_add]
    by_cases hsc : scaled r (vecF n') a
    · -- a scaled variable: pair it with the `Tp` of its late letter
      obtain ⟨y₀, hy₀S, hy₀⟩ : ∃ y₀ ∈ S, posOf n' y₀.2 = a.1 := by
        have h := hF.sum_late (M := ℕ) (fun t => if t = a.1 then 1 else 0)
        rw [sum_ite_eq' TT a.1 (fun _ => 1), ite_eq_left ha] at h
        obtain ⟨j, hj, hj'⟩ := exists_ne_zero_of_sum_ne_zero (h.symm ▸ one_ne_zero)
        obtain ⟨x, hx, hx'⟩ := exists_ne_zero_of_sum_ne_zero hj'
        exact ⟨⟨j, x⟩, mem_sigma.2 ⟨hj, hx⟩, by simpa using hx'⟩
      have hb' : b ≤ ν y₀ := by
        have h := hν y₀ hy₀S
        rw [piDeg_add, piDeg_single, hy₀, ite_eq_left ⟨rfl, hsc⟩] at h
        omega
      set ν' := Function.update ν y₀ (ν y₀ - b) with hν'
      have hν'S : ∀ y ∈ S, piDeg r (vecF n') f (posOf n' y.2) ≤ ν' y := by
        intro y hy
        have h := hν y hy
        rw [piDeg_add, piDeg_single] at h
        by_cases hyy : y = y₀
        · subst hyy
          rw [hν', Function.update_self, hy₀]
          rw [hy₀, ite_eq_left ⟨rfl, hsc⟩] at h
          omega
        · rw [hν', Function.update_of_ne hyy]
          omega
      have hsplit : ∏ y ∈ S, Tp F TT Kf p K y.1 y.2 ^ ν y =
          Tp F TT Kf p K y₀.1 y₀.2 ^ b * ∏ y ∈ S, Tp F TT Kf p K y.1 y.2 ^ ν' y := by
        rw [← mul_prod_erase _ _ hy₀S, ← mul_prod_erase _ _ hy₀S, hν', Function.update_self, ← mul_assoc, ← pow_add,
          Nat.add_sub_cancel' hb']
        congr 1
        exact prod_congr rfl fun y hy => by rw [Function.update_of_ne (ne_of_mem_erase hy)]
      have hkey : (C (algebraMap O Kf ϖ) * X a * Tp F TT Kf p K y₀.1 y₀.2) ^ b ∈
          AddSubmonoid.closure (keyGens W ι σ ϖ TT Q b) := by
        refine pow_mem_closure ?_ b
        have hx := (mem_sigma.1 hy₀S).2
        have e : a = (posOf n' y₀.2, a.2) := by rw [hy₀]
        rw [e]
        exact scaled_var_mem hU hn hp hF hQ hx (by rw [hy₀]; exact hsc)
      have h := closure_keyGens_mul hkey (ih hf ν' hν'S)
      rw [hndm, ite_eq_left hsc, hsplit]
      convert h using 1
      rw [pow_add, map_mul, map_pow, mul_pow, mul_pow]
      ring
    · -- an unscaled variable: an unscaled factor
      have hν'S : ∀ y ∈ S, piDeg r (vecF n') f (posOf n' y.2) ≤ ν y := fun y hy => by
        have h := hν y hy
        rw [piDeg_add] at h
        omega
      have hXU : Unscaled ϖ TT ((X a : LPol (Fin n') (r + K) Kf) ^ b) := by
        refine ⟨by simpa using ordGe_pow (ordGe_X (ϖ := ϖ) (Kf := Kf) a) b, Subalgebra.pow_mem _
          (X_mem_supported.2 (show a ∈ {v : Fin n' × Fin (r + K) | v.1 ∈ TT} from ha)) _, hom_iff.2 ?_⟩
        simpa [scW, hsc] using (isWeightedHomogeneous_X Kf (scW r) a).pow b
      have h := closure_keyGens_mul (AddSubmonoid.subset_closure (unscaled_mem_keyGens (W := W) (ι := ι) (σ := σ)
        (Q := Q) hXU)) (ih hf ν hν'S)
      rw [zero_add] at h
      rw [hndm, ite_eq_right hsc, zero_add]
      convert h using 1
      ring

/-- **Conversion** (the cofactor identities, used on error terms): a scaled monomial with its `ϖ`-power, times one
`Tp` per scaled variable at each top, is a sum of generators of level `nd m` (Tp-keys at even letters, odd keys through
`odd_cofactor_identity`). -/
theorem monomial_conversion (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p)
    {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q)
    (m : Fin n' × Fin (r + K) →₀ ℕ) (hm : ∀ v ∈ m.support, v.1 ∈ TT) (ν : ℕ)
    (hν : ∀ s, piDeg r (vecF n') m s ≤ ν) :
    (algebraMap O Kf ϖ ^ nd r (vecF n') m) • monomial m (1 : Kf) * budgetProd F TT Kf p K ^ ν ∈
      AddSubmonoid.closure (keyGens W ι σ ϖ TT Q (nd r (vecF n') m)) := by
  have h := conv_gen hU hn hp hF hQ m hm (fun _ => ν) fun y _ => hν _
  rw [budgetProd, ← prod_pow, smul_eq_C_mul]
  rw [prod_sigma] at h
  simpa only [prod_pow] using h

end Conversion

/-! ## Realisable polynomials and the iteration -/

section Iterate

variable (W ι σ ϖ) in
/-- **Realisable to precision `t`** (main edge): `P ≡ Φ_1 G (mod ϖ^t)` for an integral `G` with `ord_{g′} G ≥ t` at
every `g′` off the plane; an additive subgroup. -/
def realSub (p n' r K t : ℕ) : AddSubgroup (LPol (Fin n') (r + K) Kf) where
  carrier := {P | ∃ G, OrdGe ϖ 0 G ∧ OrdGe ϖ t (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) G - P) ∧
    ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, OffPlane p g' → OrdGe ϖ t (ad ι σ ϖ n' r K g' G)}
  zero_mem' := ⟨0, ordGe_zero 0, by simpa using ordGe_zero t, fun _ _ => by simpa using ordGe_zero t⟩
  add_mem' := by
    rintro P P' ⟨G, h1, h2, h3⟩ ⟨G', h1', h2', h3'⟩
    refine ⟨G + G', ordGe_add h1 h1', ?_, fun g' hg => ?_⟩
    · rw [map_add]
      convert ordGe_add h2 h2' using 1
      ring
    · rw [map_add]
      exact ordGe_add (h3 g' hg) (h3' g' hg)
  neg_mem' := by
    rintro P ⟨G, h1, h2, h3⟩
    refine ⟨-G, ordGe_neg h1, ?_, fun g' hg => ?_⟩
    · rw [map_neg]
      convert ordGe_neg h2 using 1
      ring
    · rw [map_neg]
      exact ordGe_neg (h3 g' hg)

/-- **Small polynomials are realisable** (by `0`). -/
theorem realSub_of_ordGe {t : ℕ} {P : LPol (Fin n') (r + K) Kf} (h : OrdGe ϖ t P) : P ∈ realSub W ι σ ϖ p n' r K t :=
  ⟨0, ordGe_zero 0, by simpa using ordGe_neg h, fun _ _ => by simpa using ordGe_zero t⟩

/-- **Lifts of small raw polynomials are realisable** (by themselves). -/
theorem realSub_of_raw {t : ℕ} {G : LPol (Fin n') (r + K) Kf} (hG : OrdGe ϖ 0 G)
    (hs : ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, OffPlane p g' → OrdGe ϖ t (ad ι σ ϖ n' r K g' G)) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) G ∈ realSub W ι σ ϖ p n' r K t :=
  ⟨G, hG, by simpa using ordGe_zero t, hs⟩

/-- **The iteration lemma** (abstract): raw lifts that are small off the plane to precision `t` and whose
`Φ_1`-errors are, modulo `ϖ^t`, sums of strictly higher-level symbols, realise every symbol to precision `t`. -/
theorem iterate {Ix : Type*} (lev : Ix → ℕ) (sym raw : Ix → LPol (Fin n') (r + K) Kf) (t : ℕ)
    (hsym : ∀ τ, OrdGe ϖ (lev τ) (sym τ))
    (hraw : ∀ τ, lev τ < t → OrdGe ϖ 0 (raw τ) ∧
      ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, OffPlane p g' → OrdGe ϖ t (ad ι σ ϖ n' r K g' (raw τ)))
    (herr : ∀ τ, lev τ < t → ∃ s : Finset Ix, (∀ τ' ∈ s, lev τ < lev τ') ∧
      OrdGe ϖ t (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (raw τ) - sym τ - ∑ τ' ∈ s, sym τ'))
    (τ : Ix) :
    ∃ G : LPol (Fin n') (r + K) Kf, OrdGe ϖ 0 G ∧
      OrdGe ϖ t (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) G - sym τ) ∧
      ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, OffPlane p g' → OrdGe ϖ t (ad ι σ ϖ n' r K g' G) := by
  suffices h : ∀ n τ, t - lev τ ≤ n → sym τ ∈ realSub W ι σ ϖ p n' r K t from h _ τ le_rfl
  intro n
  induction n with
  | zero =>
    intro τ hτ
    exact realSub_of_ordGe (ordGe_mono (by omega) (hsym τ))
  | succ n ih =>
    intro τ hτ
    by_cases hlt : lev τ < t
    · obtain ⟨s, hs, herr'⟩ := herr τ hlt
      have e : sym τ = ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (raw τ) -
          (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (raw τ) - sym τ - ∑ τ' ∈ s, sym τ') -
          ∑ τ' ∈ s, sym τ' := by ring
      rw [e]
      refine AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (realSub_of_raw (hraw τ hlt).1 (hraw τ hlt).2)
        (realSub_of_ordGe herr')) (AddSubgroup.sum_mem _ fun τ' hτ' => ih τ' ?_)
      have := hs τ' hτ'
      omega
    · exact realSub_of_ordGe (ordGe_mono (by omega) (hsym τ))

end Iterate

/-! ## Key products -/

section KeyProd

/-- **Keys**: a key `κ`, its leading form `κ₀` and its level. -/
abbrev KeyT (n' r K : ℕ) (Kf : Type) [Field Kf] := LPol (Fin n') (r + K) Kf × LPol (Fin n') (r + K) Kf × ℕ

/-- **Leading forms of keys are graded-integral.** -/
theorem lead_gInt {TT : Finset (Fin n')} {Q : ℕ} {y : KeyT n' r K Kf} (hy : IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2) :
    y.2.1 ∈ gInt ϖ r (vecF n') :=
  gInt_of_hom hy.hom hy.lead

/-- **The key product has order the sum of the levels.** -/
theorem ordGe_keyprod {TT : Finset (Fin n')} {Q : ℕ} {ks : List (KeyT n' r K Kf)}
    (hks : ∀ y ∈ ks, IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2) :
    OrdGe ϖ (ks.map fun y => y.2.2).sum (ks.map fun y => y.2.1).prod := by
  induction ks with
  | nil => simpa using ordGe_one
  | cons y ks ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ordGe_mul (hks y List.mem_cons_self).lead (ih fun y' hy' => hks y' (List.mem_cons_of_mem _ hy'))

/-- **The key product is graded-integral and on the tops.** -/
theorem keyprod_gInt {TT : Finset (Fin n')} {Q : ℕ} {ks : List (KeyT n' r K Kf)}
    (hks : ∀ y ∈ ks, IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2) :
    (ks.map fun y => y.2.1).prod ∈ gInt ϖ r (vecF n') ∧
      (ks.map fun y => y.2.1).prod ∈ supported Kf {v | v.1 ∈ TT} := by
  induction ks with
  | nil => exact ⟨by simp, by simp⟩
  | cons y ks ih =>
    simp only [List.map_cons, List.prod_cons]
    have ih' := ih fun y' hy' => hks y' (List.mem_cons_of_mem _ hy')
    exact ⟨Subalgebra.mul_mem _ (lead_gInt (hks y List.mem_cons_self)) ih'.1,
      Subalgebra.mul_mem _ (hks y List.mem_cons_self).lead_tops ih'.2⟩

end KeyProd

/-! ## Terms of the realisation -/

section Terms

variable [NeZero n'] [NeZero r]

/-- **The level of a term** `ϖ^i·∏κ⁰_l·…`: `i + Σ_l o_l`. -/
def levT (i : ℕ) (ks : List (KeyT n' r K Kf)) : ℕ := i + (ks.map fun y => y.2.2).sum

variable (ϖ) in
/-- **The symbol of a term**: `ϖ^i·∏κ⁰_l·Ξ⁰^a·budgetProd^μ·h`. -/
def symT (F : FrameSys n' r) (TT : Finset (Fin n')) (i : ℕ) (ks : List (KeyT n' r K Kf)) (a μ : ℕ)
    (h : LPol (Fin n') (r + K) Kf) : LPol (Fin n') (r + K) Kf :=
  C (algebraMap O Kf ϖ ^ i) * (ks.map fun y => y.2.1).prod * locLead F Kf p K ^ a * budgetProd F TT Kf p K ^ μ * h

variable (ϖ) in
/-- **The raw lift of a term**: `ϖ^i·∏κ_l·Ξ_loc^a·budgetProd^μ·h`. -/
def rawT (F : FrameSys n' r) (TT : Finset (Fin n')) (i : ℕ) (ks : List (KeyT n' r K Kf)) (a μ : ℕ)
    (h : LPol (Fin n') (r + K) Kf) : LPol (Fin n') (r + K) Kf :=
  C (algebraMap O Kf ϖ ^ i) * (ks.map fun y => y.1).prod * locPoly F Kf p K ^ a * budgetProd F TT Kf p K ^ μ * h

variable (W ι σ ϖ) in
/-- **A valid term** for precision `t`: keys, an unscaled `h`, localiser exponent `a ≥ t − lev` and budget
`μ ≥ (2Q + 1)(t − lev)`. -/
def ValidT (TT : Finset (Fin n')) (Q t i : ℕ) (ks : List (KeyT n' r K Kf)) (a μ : ℕ) (h : LPol (Fin n') (r + K) Kf) :
    Prop :=
  (∀ y ∈ ks, IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2) ∧ Unscaled ϖ TT h ∧ t - levT i ks ≤ a ∧
    (2 * Q + 1) * (t - levT i ks) ≤ μ

variable [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O]

omit [NeZero n'] [NeZero r] in
/-- **The expansion of the keys at `g = 1`** (no subsets): `∏Φ_1κ_l − ∏κ⁰_l` is a sum of `∏_{l ∈ U}κ⁰_l·P` over
untouched sublists `U`, with `P` graded-integral of order `d + s`, `s ≥ 1` touched keys of total level `d ≤ 2Qs`. -/
theorem keys_expand (hU : Unram p n' W Qq O Kf ι σ jW ϖ) {TT : Finset (Fin n')} {Q : ℕ}
    (ks : List (KeyT n' r K Kf)) (hks : ∀ y ∈ ks, IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2) :
    ∃ L : List (List (KeyT n' r K Kf) × ℕ × ℕ × LPol (Fin n') (r + K) Kf),
      (ks.map fun y => ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) y.1).prod -
          (ks.map fun y => y.2.1).prod = (L.map fun x => (x.1.map fun y => y.2.1).prod * x.2.2.2).sum ∧
      ∀ x ∈ L, (∀ y ∈ x.1, y ∈ ks) ∧ 1 ≤ x.2.2.1 ∧ x.2.1 ≤ 2 * Q * x.2.2.1 ∧
        x.2.1 + (x.1.map fun y => y.2.2).sum = (ks.map fun y => y.2.2).sum ∧ x.2.2.2 ∈ gInt ϖ r (vecF n') ∧
        OrdGe ϖ (x.2.1 + x.2.2.1) x.2.2.2 ∧ x.2.2.2 ∈ supported Kf {v | v.1 ∈ TT} := by
  induction ks with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons k ks ih =>
    obtain ⟨L, hL, hLp⟩ := ih fun y hy => hks y (List.mem_cons_of_mem _ hy)
    have hk := hks k List.mem_cons_self
    set E := ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) k.1 - k.2.1 with hE
    have hEg : E ∈ gInt ϖ r (vecF n') :=
      Subalgebra.sub_mem _ (liftSub_mem_gInt hU r _ _ _ hk.int) (lead_gInt hk)
    have hEt : E ∈ supported Kf {v | v.1 ∈ TT} := Subalgebra.sub_mem _ (ad_one_mem_tops hk.tops) hk.lead_tops
    refine ⟨L.map (fun x => (k :: x.1, x.2.1, x.2.2.1, x.2.2.2)) ++ [(ks, k.2.2, 1, E)] ++
      L.map (fun x => (x.1, x.2.1 + k.2.2, x.2.2.1 + 1, E * x.2.2.2)), ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, List.map_append, List.sum_append, List.map_map, List.map_nil,
        List.sum_cons, List.sum_nil, Function.comp_def]
      have e1 : (L.map fun x => k.2.1 * (x.1.map fun y => y.2.1).prod * x.2.2.2).sum =
          k.2.1 * (L.map fun x => (x.1.map fun y => y.2.1).prod * x.2.2.2).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        exact List.map_congr_left fun x _ => by ring
      have e2 : (L.map fun x => (x.1.map fun y => y.2.1).prod * (E * x.2.2.2)).sum =
          E * (L.map fun x => (x.1.map fun y => y.2.1).prod * x.2.2.2).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        exact List.map_congr_left fun x _ => by ring
      rw [e1, e2, ← hL, hE]
      ring
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hLp x' hx'
          refine ⟨fun y hy => ?_, h2, h3, ?_, h5, h6, h7⟩
          · rcases List.mem_cons.1 hy with rfl | hy
            exacts [List.mem_cons_self, List.mem_cons_of_mem _ (h1 y hy)]
          · simp only [List.map_cons, List.sum_cons]
            omega
        · rw [List.mem_singleton] at hx
          subst hx
          refine ⟨fun y hy => List.mem_cons_of_mem _ hy, le_rfl, by simpa using hk.le, by simp, hEg, ?_, hEt⟩
          simpa using hk.err
      · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hLp x' hx'
        refine ⟨fun y hy => List.mem_cons_of_mem _ (h1 y hy), Nat.le_add_left 1 _, ?_, ?_,
          Subalgebra.mul_mem _ hEg h5, ?_, Subalgebra.mul_mem _ hEt h7⟩
        · have := hk.le
          nlinarith
        · simp only [List.map_cons, List.sum_cons]
          omega
        · have := ordGe_mul hk.err h6
          show OrdGe ϖ ((x'.2.1 + k.2.2) + (x'.2.2.1 + 1)) (E * x'.2.2.2)
          rw [show (x'.2.1 + k.2.2) + (x'.2.2.1 + 1) = k.2.2 + 1 + (x'.2.1 + x'.2.2.1) by ring]
          exact this

end Terms

/-! ## One step of the realisation -/

section Step

variable [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O]

omit [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The `ϖ`-degree at one letter is at most the total.** -/
theorem piDeg_le_nd [NeZero n'] (m : Fin n' × Fin (r + K) →₀ ℕ) (s : Fin n') :
    piDeg r (vecF n') m s ≤ nd r (vecF n') m := by
  rw [← sum_piDeg]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ s)

omit [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Monomials of order `v`.** -/
theorem ordGe_monomial (m : Fin n' × Fin (r + K) →₀ ℕ) (v : ℕ) (u : O) :
    OrdGe ϖ v (monomial m (algebraMap O Kf (ϖ ^ v * u))) := fun m' => by
  classical
  refine ⟨if m = m' then u else 0, ?_⟩
  rw [coeff_monomial]
  split_ifs <;> simp

omit [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Monomials of a polynomial on the tops live on the tops.** -/
theorem support_tops {TT : Finset (Fin n')} {P : LPol (Fin n') (r + K) Kf} (hP : P ∈ supported Kf {v | v.1 ∈ TT})
    {m : Fin n' × Fin (r + K) →₀ ℕ} (hm : m ∈ P.support) : ∀ w ∈ m.support, w.1 ∈ TT := fun w hw => by
  classical
  rw [mem_supported] at hP
  exact hP (Finset.mem_coe.2 ((mem_vars_iff_mem_support w).2 ⟨m, hm, hw⟩))

/-- **The localiser error** `R = Φ_1 Ξ_loc − Ξ⁰`: graded-integral, of order `1`, on the tops. -/
theorem locErr (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K) - locLead F Kf p K ∈
        gInt ϖ r (vecF n') ∧
      OrdGe ϖ 1 (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K) - locLead F Kf p K) ∧
      ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K) - locLead F Kf p K ∈
        supported Kf {v | v.1 ∈ TT} := by
  obtain ⟨hLi, hLs, -, hli, hls, hlnd⟩ := explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF
  obtain ⟨-, hdiff⟩ := locPoly_sub_locLead (Kf := Kf) (K := K) hn hp hF
  refine ⟨Subalgebra.sub_mem _ (liftSub_mem_gInt hU r _ _ _ hLi) (gInt_of_hom hlnd hli), ?_,
    Subalgebra.sub_mem _ (ad_one_mem_tops hLs) hls⟩
  have e : ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K) - locLead F Kf p K =
      ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K - locLead F Kf p K) := by
    rw [map_sub, ad_one_of_nd hlnd]
  rw [e]
  intro m
  rw [coeff_ad_one]
  obtain ⟨c, hc⟩ := ordGe_sub hLi hli m
  by_cases hm : m ∈ (locPoly F Kf p K - locLead F Kf p K).support
  · have h1 := hdiff m hm
    refine ⟨ϖ ^ (nd r (vecF n') m - 1) * c, ?_⟩
    rw [hc, pow_zero, one_mul, ← map_pow, ← map_mul]
    congr 1
    conv_lhs => rw [show nd r (vecF n') m = 1 + (nd r (vecF n') m - 1) by omega]
    ring
  · exact ⟨0, by rw [notMem_support_iff.1 hm, zero_mul, mul_zero, map_zero]⟩

/-- **A pre-term is realisable** (the conversion step): `ϖ^i·∏_{l ∈ U}κ⁰_l·Ξ⁰^a·budgetProd^μ·h·P`, with `P`
graded-integral of order `d + s` on the tops (`s ≥ 1` touched keys of level `d ≤ 2Qs`, base level
`ℓ₀ = lev + d`), is a sum of symbols of terms of level `> ℓ₀` modulo `ϖ^t`: each monomial of `P` is converted,
consuming at most `(2Q + 1)·(level gain)` of the budget. -/
theorem preterm_mem (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) {t ℓ₀ : ℕ}
    (IH : ∀ i ks a μ h, ValidT W ι σ ϖ TT Q t i ks a μ h → ℓ₀ < levT i ks →
      symT ϖ F TT (p := p) i ks a μ h ∈ realSub W ι σ ϖ p n' r K t)
    {i : ℕ} {U : List (KeyT n' r K Kf)} (hUk : ∀ y ∈ U, IsPlaneKey W ι σ ϖ TT Q y.1 y.2.1 y.2.2)
    {a μ : ℕ} {h : LPol (Fin n') (r + K) Kf} (hh : Unscaled ϖ TT h) {d s : ℕ} {P : LPol (Fin n') (r + K) Kf}
    (hs : 1 ≤ s) (hd : d ≤ 2 * Q * s) (hPg : P ∈ gInt ϖ r (vecF n')) (hPo : OrdGe ϖ (d + s) P)
    (hPt : P ∈ supported Kf {v | v.1 ∈ TT}) (hℓ : ℓ₀ = levT i U + d) (ha : t - ℓ₀ ≤ a + s)
    (hμ : (2 * Q + 1) * (t - ℓ₀) ≤ μ) :
    C (algebraMap O Kf ϖ ^ i) * (U.map fun y => y.2.1).prod * locLead F Kf p K ^ a * budgetProd F TT Kf p K ^ μ *
      h * P ∈ realSub W ι σ ϖ p n' r K t := by
  classical
  obtain ⟨hLi, -, ⟨hBi, -, -⟩, -⟩ := explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF
  have hLLi : OrdGe ϖ 0 (locLead F Kf p K) := (explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF).2.2.2.1
  rw [P.as_sum, mul_sum]
  refine AddSubgroup.sum_mem _ fun m hm => ?_
  obtain ⟨v, u, hcv, hv1, hv2⟩ : ∃ v u, P.coeff m = algebraMap O Kf (ϖ ^ v * u) ∧ nd r (vecF n') m ≤ v ∧
      d + s ≤ v := by
    obtain ⟨c1, h1⟩ := hPg m
    obtain ⟨c2, h2⟩ := hPo m
    by_cases hle : d + s ≤ nd r (vecF n') m
    · exact ⟨nd r (vecF n') m, c1, h1, le_rfl, hle⟩
    · exact ⟨d + s, c2, h2, by omega, le_rfl⟩
  have hmt := support_tops hPt hm
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ', ℓ' = levT i U + v := ⟨_, rfl⟩
  have hkeys := ordGe_keyprod hUk
  rw [hcv]
  by_cases hlt : t ≤ ℓ'
  · apply realSub_of_ordGe
    have h1 := ordGe_mul (ordGe_mul (ordGe_mul (ordGe_mul (ordGe_mul (ordGe_C (τ := Fin n' × Fin (r + K))
      (ϖ := ϖ) (Kf := Kf) i 1) hkeys) (ordGe_pow hLLi a)) (ordGe_pow hBi μ)) hh.1) (ordGe_monomial m v u)
    refine ordGe_mono hlt ?_
    rw [hℓ', levT]
    simpa only [mul_one, mul_zero, add_zero, map_pow] using h1
  · push Not at hlt
    have hgain : s ≤ ℓ' - ℓ₀ := by omega
    have hnd : nd r (vecF n') m ≤ (2 * Q + 1) * (ℓ' - ℓ₀) := by
      have h1 : 2 * Q * s ≤ 2 * Q * (ℓ' - ℓ₀) := Nat.mul_le_mul_left _ hgain
      have h2 : (2 * Q + 1) * (ℓ' - ℓ₀) = 2 * Q * (ℓ' - ℓ₀) + (ℓ' - ℓ₀) := by ring
      omega
    have hmono : (2 * Q + 1) * (ℓ' - ℓ₀) ≤ (2 * Q + 1) * (t - ℓ₀) := Nat.mul_le_mul_left _ (by omega)
    have hndμ : nd r (vecF n') m ≤ μ := by omega
    have hsplit : (2 * Q + 1) * (t - ℓ') + (2 * Q + 1) * (ℓ' - ℓ₀) = (2 * Q + 1) * (t - ℓ₀) := by
      rw [← mul_add]
      congr 1
      omega
    have key : ∀ z ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q (nd r (vecF n') m)),
        C (algebraMap O Kf ϖ ^ i) * (U.map fun y => y.2.1).prod * locLead F Kf p K ^ a *
          budgetProd F TT Kf p K ^ (μ - nd r (vecF n') m) *
          (h * C (algebraMap O Kf (ϖ ^ (v - nd r (vecF n') m) * u))) * z ∈ realSub W ι σ ϖ p n' r K t := by
      intro z hz
      induction hz using AddSubmonoid.closure_induction with
      | mem z hz =>
        obtain ⟨A, h', ⟨l, hl, rfl, hlo⟩, hh', rfl⟩ := hz
        have hlev : levT (i + (v - nd r (vecF n') m)) (U ++ l) = ℓ' := by
          have hlo' : (l.map fun y : KeyT n' r K Kf => y.2.2).sum = nd r (vecF n') m := hlo.symm
          simp only [levT, List.map_append, List.sum_append] at hℓ' ⊢
          rw [hlo']
          omega
        have hval : ValidT W ι σ ϖ TT Q t (i + (v - nd r (vecF n') m)) (U ++ l) a (μ - nd r (vecF n') m)
            (C (algebraMap O Kf u) * h * h') := by
          refine ⟨fun y hy => ?_, unscaled_mul (unscaled_mul (unscaled_C u) hh) hh', ?_, ?_⟩
          · rcases List.mem_append.1 hy with hy | hy
            exacts [hUk y hy, hl y hy]
          · rw [hlev]
            omega
          · rw [hlev]
            omega
        have := IH _ _ _ _ _ hval (by rw [hlev]; omega)
        convert this using 1
        simp only [symT, List.map_append, List.prod_append, map_mul, map_pow]
        conv_lhs => rw [show v - nd r (vecF n') m = v - nd r (vecF n') m from rfl]
        rw [pow_add]
        ring
      | zero => simp
      | add z z' _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
    have hconv := monomial_conversion hU hn hp hF hQ m hmt (nd r (vecF n') m) fun s' => piDeg_le_nd m s'
    convert key _ hconv using 1
    have e1 : (monomial m (algebraMap O Kf (ϖ ^ v * u)) : LPol (Fin n') (r + K) Kf) =
        C (algebraMap O Kf (ϖ ^ (v - nd r (vecF n') m) * u)) * (C (algebraMap O Kf ϖ ^ nd r (vecF n') m) *
          monomial m 1) := by
      rw [C_mul_monomial, C_mul_monomial, mul_one, ← map_pow, ← map_mul]
      congr 2
      conv_lhs => rw [show v = (v - nd r (vecF n') m) + nd r (vecF n') m by omega]
      ring
    have e2 : budgetProd F TT Kf p K ^ μ =
        budgetProd F TT Kf p K ^ (μ - nd r (vecF n') m) * budgetProd F TT Kf p K ^ nd r (vecF n') m := by
      rw [← pow_add, Nat.sub_add_cancel hndμ]
    rw [e1, e2, smul_eq_C_mul]
    ring

omit [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Natural numbers are unscaled.** -/
theorem unscaled_natCast {TT : Finset (Fin n')} (k : ℕ) : Unscaled ϖ TT (k : LPol (Fin n') (r + K) Kf) := by
  have e : (k : LPol (Fin n') (r + K) Kf) = C (algebraMap O Kf (k : O)) := by rw [map_natCast, map_natCast]
  rw [e]
  exact unscaled_C _

omit [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Orders of list products.** -/
theorem ordGe_listprod {β : Type*} (l : List β) (f : β → ℕ) (g : β → LPol (Fin n') (r + K) Kf)
    (h : ∀ y ∈ l, OrdGe ϖ (f y) (g y)) : OrdGe ϖ (l.map f).sum (l.map g).prod := by
  induction l with
  | nil => simpa using ordGe_one
  | cons y l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    exact ordGe_mul (h y List.mem_cons_self) (ih fun y' hy' => h y' (List.mem_cons_of_mem _ hy'))

/-- **One step of the realisation**: for a valid term below the precision, `Φ_1(raw) − sym` is, modulo `ϖ^t`, a
sum of pre-terms (one per touched key set and localiser power), all of base level `lev`; so if every valid term of
higher level is realisable, so is this one. -/
theorem step_mem (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) {t i : ℕ} {ks : List (KeyT n' r K Kf)}
    {a μ : ℕ} {h : LPol (Fin n') (r + K) Kf} (hv : ValidT W ι σ ϖ TT Q t i ks a μ h) (hlt : levT i ks < t)
    (IH : ∀ i' ks' a' μ' h', ValidT W ι σ ϖ TT Q t i' ks' a' μ' h' → levT i ks < levT i' ks' →
      symT ϖ F TT (p := p) i' ks' a' μ' h' ∈ realSub W ι σ ϖ p n' r K t) :
    symT ϖ F TT (p := p) i ks a μ h ∈ realSub W ι σ ϖ p n' r K t := by
  classical
  obtain ⟨hks, hh, ha, hμ⟩ := hv
  obtain ⟨hLi, hLs, ⟨hBi, -, hBnd⟩, hLLi, -, hLLnd⟩ := explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF
  obtain ⟨hRg, hRo, hRt⟩ := locErr (ϖ := ϖ) (K := K) hU hn hp hF
  obtain ⟨L, hL, hLp⟩ := keys_expand hU ks hks
  set Λ := locLead F Kf p K with hΛ
  set R := ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K) - Λ with hR
  set B := budgetProd F TT Kf p K with hB
  set c0 := C (algebraMap O Kf ϖ ^ i) * B ^ μ * h with hc0
  have hC : OrdGe ϖ 0 (C (algebraMap O Kf ϖ ^ i) : LPol (Fin n') (r + K) Kf) := by
    rw [← map_pow]
    exact ordGe_C_int _
  have hCi : OrdGe ϖ i (C (algebraMap O Kf ϖ ^ i) : LPol (Fin n') (r + K) Kf) := by
    simpa using ordGe_C (τ := Fin n' × Fin (r + K)) (ϖ := ϖ) (Kf := Kf) i 1
  -- the raw lift
  have hrawI : OrdGe ϖ 0 (rawT ϖ F TT (p := p) i ks a μ h) := by
    have hK : OrdGe ϖ 0 ((ks.map fun y => y.1).prod) := by
      simpa using ordGe_listprod (ϖ := ϖ) ks (fun _ => 0) (fun y => y.1) fun y hy => (hks y hy).int
    rw [rawT]
    simpa using ordGe_mul (ordGe_mul (ordGe_mul (ordGe_mul hC hK) (ordGe_pow hLi a)) (ordGe_pow hBi μ)) hh.1
  have hrawS : ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, OffPlane p g' →
      OrdGe ϖ t (ad ι σ ϖ n' r K g' (rawT ϖ F TT (p := p) i ks a μ h)) := by
    intro g' hg'
    have h1 := ordGe_mul (ordGe_mul (ordGe_mul (ordGe_mul hCi
      (ordGe_listprod (ϖ := ϖ) ks (fun y => y.2.2) (fun y => ad ι σ ϖ n' r K g' y.1)
        fun y hy => (hks y hy).small g' hg'.1)) (ordGe_pow (locPoly_offPlane hU hn hF g' hg') a))
      (ordGe_pow (ordGe_liftSub (r := r) hU (vecF n') (fun s => s.val) g' hBi) μ))
      (ordGe_liftSub (r := r) hU (vecF n') (fun s => s.val) g' hh.1)
    refine ordGe_mono (i := i + (ks.map fun y => y.2.2).sum + a) (by simp only [levT] at ha hlt; omega) ?_
    rw [rawT, map_mul, map_mul, map_mul, map_mul, algHom_C, map_list_prod, List.map_map, map_pow, map_pow]
    simpa [Function.comp_def] using h1
  have hadraw : ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (rawT ϖ F TT (p := p) i ks a μ h) =
      C (algebraMap O Kf ϖ ^ i) * (ks.map fun y => ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W)
        y.1).prod * (Λ + R) ^ a * B ^ μ * h := by
    have hlp : ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (locPoly F Kf p K) = Λ + R := by
      rw [hR]
      ring
    rw [rawT, map_mul, map_mul, map_mul, map_mul, algHom_C, map_list_prod, List.map_map, map_pow (f := ad _ _ _ _ _ _ _)
      (locPoly F Kf p K), map_pow (f := ad _ _ _ _ _ _ _) B, ad_one_of_nd hBnd, ad_one_of_nd hh.2.2, hlp]
    rfl
  have e : symT ϖ F TT (p := p) i ks a μ h =
      ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (rawT ϖ F TT (p := p) i ks a μ h) -
      (c0 * (ks.map fun y => y.2.1).prod * ((R + Λ) ^ a - Λ ^ a) +
        c0 * ((ks.map fun y => ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) y.1).prod -
          (ks.map fun y => y.2.1).prod) * (R + Λ) ^ a) := by
    rw [hadraw, symT, hc0]
    ring
  rw [e]
  refine AddSubgroup.sub_mem _ (realSub_of_raw hrawI hrawS) (AddSubgroup.add_mem _ ?_ ?_)
  · -- the localiser errors at untouched keys
    rw [add_pow, sum_range_succ', pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      add_sub_cancel_right, mul_sum]
    refine AddSubgroup.sum_mem _ fun m hm => ?_
    have hm' := mem_range.1 hm
    have := preterm_mem hU hn hp hF hQ (ℓ₀ := levT i ks) IH (i := i) hks (a := a - (m + 1)) (μ := μ)
      (unscaled_mul hh (unscaled_natCast (a.choose (m + 1)))) (d := 0) (s := m + 1) (P := R ^ (m + 1))
      (by omega) (by simp) (Subalgebra.pow_mem _ hRg _) (by simpa using ordGe_pow hRo (m + 1))
      (Subalgebra.pow_mem _ hRt _) (by simp) (by omega) hμ
    convert this using 1
    rw [hc0]
    ring
  · -- the touched keys
    rw [hL, add_pow]
    have e2 : c0 * (L.map fun x => (x.1.map fun y => y.2.1).prod * x.2.2.2).sum *
        ∑ m ∈ range (a + 1), R ^ m * Λ ^ (a - m) * (a.choose m : LPol (Fin n') (r + K) Kf) =
        (L.map fun x => ∑ m ∈ range (a + 1), c0 * ((x.1.map fun y => y.2.1).prod * x.2.2.2) *
          (R ^ m * Λ ^ (a - m) * (a.choose m : LPol (Fin n') (r + K) Kf))).sum := by
      rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
      congr 1
      refine List.map_congr_left fun x _ => ?_
      rw [mul_sum]
    rw [e2]
    refine AddSubgroup.list_sum_mem _ fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hLp x hx
    refine AddSubgroup.sum_mem _ fun m hm => ?_
    have hm' := mem_range.1 hm
    have := preterm_mem hU hn hp hF hQ (ℓ₀ := levT i ks) IH (i := i) (fun y hy => hks y (h1 y hy)) (a := a - m)
      (μ := μ)
      (unscaled_mul hh (unscaled_natCast (a.choose m))) (d := x.2.1) (s := x.2.2.1 + m) (P := x.2.2.2 * R ^ m)
      (by omega) (by nlinarith) (Subalgebra.mul_mem _ h5 (Subalgebra.pow_mem _ hRg _))
      (by have := ordGe_mul h6 (ordGe_pow hRo m); simpa [add_assoc] using this)
      (Subalgebra.mul_mem _ h7 (Subalgebra.pow_mem _ hRt _)) (by simp only [levT]; omega) (by omega) hμ
    convert this using 1
    rw [hc0]
    ring

/-- **Every valid term is realisable** (downward induction on the level). -/
theorem valid_mem (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) (t : ℕ) :
    ∀ N i ks a μ h, ValidT W ι σ ϖ TT Q t i ks a μ h → t - levT i ks ≤ N →
      symT ϖ F TT (p := p) i ks a μ h ∈ realSub W ι σ ϖ p n' r K t := by
  intro N
  induction N with
  | zero =>
    intro i ks a μ h hv hN
    obtain ⟨hks, hh, -, -⟩ := hv
    obtain ⟨-, -, ⟨hBi, -, -⟩, hLLi, -, -⟩ := explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF
    apply realSub_of_ordGe
    have h1 := ordGe_mul (ordGe_mul (ordGe_mul (ordGe_mul (ordGe_C (τ := Fin n' × Fin (r + K)) (ϖ := ϖ) (Kf := Kf)
      i 1) (ordGe_keyprod hks)) (ordGe_pow hLLi a)) (ordGe_pow hBi μ)) hh.1
    refine ordGe_mono (i := i + (ks.map fun y => y.2.2).sum) (by simp only [levT] at hN; omega) ?_
    rw [symT]
    simpa [map_pow] using h1
  | succ N ih =>
    intro i ks a μ h hv hN
    by_cases hlt : levT i ks < t
    · exact step_mem hU hn hp hF hQ hv hlt fun i' ks' a' μ' h' hv' hlev => ih _ _ _ _ _ hv' (by omega)
    · exact ih _ _ _ _ _ hv (by omega)

end Step

/-! ## The realisation core (N8 C4 at `g = 1`) -/

section Core

/-- **Components keep orders.** -/
theorem ordGe_comp {τ M : Type*} [AddCommMonoid M] [DecidableEq M] {w : τ → M} {i : ℕ} {P : MvPolynomial τ Kf}
    (hP : OrdGe ϖ i P) (d : M) : OrdGe ϖ i (weightedHomogeneousComponent w d P) := fun m => by
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hP m
  · exact ⟨0, by simp⟩

/-- **`Φ_g` commutes with letter-multidegree components** (it maps a letter's variables to the same letter's). -/
theorem ad_comp (g : Matrix (Fin (r + K)) (Fin (r + K)) W) (d : Fin n' → ℕ) (P : LPol (Fin n') (r + K) Kf) :
    ad ι σ ϖ n' r K g (weightedHomogeneousComponent (rowW (Fin n') (r + K)) d P) =
      weightedHomogeneousComponent (rowW (Fin n') (r + K)) d (ad ι σ ϖ n' r K g P) := by
  classical
  have hX : ∀ v, IsWeightedHomogeneous (rowW (Fin n') (r + K)) (ad ι σ ϖ n' r K g (X v)) (rowW (Fin n') (r + K) v) :=
    fun v => by
      simp only [ad, liftSub, aeval_X]
      refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
      simpa [rowW] using (isWeightedHomogeneous_X Kf (rowW (Fin n') (r + K)) (v.1, b)).C_mul _
  have hmon : ∀ m (c : Kf), ad ι σ ϖ n' r K g (monomial m c) ∈
      LHom Kf (Finsupp.weight (rowW (Fin n') (r + K)) m) := fun m c =>
    map_mem_LHom hX (isWeightedHomogeneous_monomial _ _ _ rfl)
  conv_rhs => rw [P.as_sum, map_sum, map_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, sum_filter]
  refine sum_congr rfl fun m _ => ?_
  rw [weightedHomogeneousComponent_of_mem (hmon m _)]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

variable [NeZero n'] [NeZero r] [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The realisation core** (C4 at `g = 1`): if `T = Z·fixFactor(c) + p^c·Y` with `Z` a sum of
key-presentable polynomials and `Y` integral, and every monomial of `T` has `ϖ`-degree `o`, then `T` is realisable
at level `o` with margin `c`. The initial terms `ϖ^0·A·Ξ⁰^c·budgetProd^{(2Q+3)c}·h` (generators `A·h` of `ϖ^o Z`)
are valid for the precision `o + c`, and every valid term is realisable (`valid_mem`); a multidegree component is
taken at the end. -/
theorem realise_core (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p)
    {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q)
    (c o : ℕ) (T Z Y : LPol (Fin n') (r + K) Kf) (hZ : Z ∈ keyPresSpan W ι σ ϖ TT Q) (hY : OrdGe ϖ 0 Y)
    (hT : T = Z * fixFactor F TT Kf p K Q c + ((p : Kf) ^ c) • Y) (ho : ∀ m ∈ T.support, nd r (vecF n') m = o) :
    RealAt (W := W) (ι := ι) (σ := σ) ϖ p c o T := by
  classical
  obtain ⟨-, -, ⟨-, -, hBnd⟩, -, -, hLLnd⟩ := explicit_int (Kf := Kf) (ϖ := ϖ) (p := p) (K := K) hn hF
  have hfix : IsWeightedHomogeneous (scW r) (fixFactor F TT Kf p K Q c) 0 := by
    have h := ((hom_iff.1 hLLnd).pow c).mul ((hom_iff.1 hBnd).pow ((2 * Q + 3) * c))
    rw [smul_zero, smul_zero, add_zero] at h
    exact h
  -- the symbol part of `ϖ^o T` is realisable
  have hZmem : ∀ Z ∈ keyPresSpan W ι σ ϖ TT Q, (algebraMap O Kf ϖ ^ o) •
      weightedHomogeneousComponent (scW r) o (Z * fixFactor F TT Kf p K Q c) ∈
        realSub W ι σ ϖ p n' r K (o + c) := by
    intro Z hZ
    induction hZ using AddSubmonoid.closure_induction with
    | mem P hP =>
      obtain ⟨o', hhom, hcl⟩ := hP
      have hPF : IsWeightedHomogeneous (scW r) (P * fixFactor F TT Kf p K Q c) o' := by
        simpa using (hom_iff.1 hhom).mul hfix
      by_cases ho' : o' = o
      · subst ho'
        rw [hPF.weightedHomogeneousComponent_same, ← smul_mul_assoc]
        have key : ∀ z ∈ AddSubmonoid.closure (keyGens W ι σ ϖ TT Q o'),
            z * fixFactor F TT Kf p K Q c ∈ realSub W ι σ ϖ p n' r K (o' + c) := by
          intro z hz
          induction hz using AddSubmonoid.closure_induction with
          | mem z hz =>
            obtain ⟨A, h, ⟨l, hl, rfl, hlo⟩, hh, rfl⟩ := hz
            have hval : ValidT W ι σ ϖ TT Q ((l.map fun y => y.2.2).sum + c) 0 l c ((2 * Q + 3) * c) h := by
              refine ⟨hl, hh, by simp [levT], ?_⟩
              simp only [levT, zero_add, Nat.add_sub_cancel_left]
              exact Nat.mul_le_mul_right _ (by omega)
            have := valid_mem hU hn hp hF hQ _ _ 0 l c ((2 * Q + 3) * c) h hval le_rfl
            rw [← hlo] at this
            convert this using 1
            simp only [symT, fixFactor, pow_zero, map_one, one_mul]
            ring
          | zero => simp
          | add x y _ _ hx hy => rw [add_mul]; exact AddSubgroup.add_mem _ hx hy
        exact key _ hcl
      · rw [hPF.weightedHomogeneousComponent_ne o (Ne.symm ho'), smul_zero]
        exact AddSubgroup.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, map_add, smul_add]; exact AddSubgroup.add_mem _ hx hy
  -- `ϖ^o T` is realisable
  have hTmem : (algebraMap O Kf ϖ ^ o) • T ∈ realSub W ι σ ϖ p n' r K (o + c) := by
    rw [← (hom_iff.1 ho).weightedHomogeneousComponent_same, hT, map_add, map_smul, smul_add]
    refine AddSubgroup.add_mem _ (hZmem Z hZ) (realSub_of_ordGe ?_)
    rw [smul_smul, smul_eq_C_mul, LocalLattice.castK_eq_sq hU, ← pow_mul, ← pow_add, ← map_pow]
    have := ordGe_mul (ordGe_C (τ := Fin n' × Fin (r + K)) (ϖ := ϖ) (Kf := Kf) (o + 2 * c) 1)
      (ordGe_comp (w := scW r) hY o)
    rw [mul_one, add_zero] at this
    exact ordGe_mono (i := o + 2 * c) (by omega) this
  obtain ⟨G, hG0, hG1, hG2⟩ := hTmem
  by_cases hT0 : T = 0
  · refine ⟨0, ordGe_zero 0, fun d _ => Submodule.zero_mem _, ?_, fun g' _ => ?_⟩
    · simpa [hT0] using ordGe_zero (ϖ := ϖ) (τ := Fin n' × Fin (r + K)) (Kf := Kf) (o + c)
    · simpa using ordGe_zero (ϖ := ϖ) (τ := Fin n' × Fin (r + K)) (Kf := Kf) (o + c)
  by_cases hd : ∃ d₀, T ∈ LHom Kf d₀
  · obtain ⟨d₀, hd₀⟩ := hd
    refine ⟨weightedHomogeneousComponent (rowW (Fin n') (r + K)) d₀ G, ordGe_comp hG0 d₀, fun d hdT => ?_, ?_,
      fun g' hg' => ?_⟩
    · obtain rfl : d = d₀ := IsWeightedHomogeneous.inj_right hT0 hdT hd₀
      exact weightedHomogeneousComponent_mem _ _ _
    · have hTd : IsWeightedHomogeneous (rowW (Fin n') (r + K)) ((algebraMap O Kf ϖ ^ o) • T) d₀ :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.smul_mem _ _ hd₀)
      rw [ad_comp, ← hTd.weightedHomogeneousComponent_same, ← map_sub]
      exact ordGe_comp hG1 d₀
    · rw [ad_comp]
      exact ordGe_comp (hG2 g' hg') d₀
  · exact ⟨G, hG0, fun d hdT => absurd ⟨d, hdT⟩ hd, hG1, hG2⟩

end Core

end

end SourceCore
