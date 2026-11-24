import Mathlib

/-!
# Names of the newer Mathlib, declared for the older one

The library is written for Lean `v4.35.0-rc3` and Mathlib at `0f64d30` (29 September 2026). The archive of the
claimed proof of the Riemann hypothesis pins Lean `v4.33.1` and Mathlib at `0df444a` (21 August 2026). This file is
for the older pair: it declares the names that the library uses and the older pair lacks, each with the statement
that the newer one gives it. The port compiles it first and every file of the port imports it
(`tools/rh/bundle_files.py --prelude`). It is not a module of the library and the repository's lakefile does not
build it.

Where the older Mathlib has the statement under another name, the name here is an alias. The other statements and
their proofs are Mathlib's, released under the Apache 2.0 license, adapted where a tactic of the newer Mathlib is
missing:

* `Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean`, Thomas Browning;
* `Mathlib/Analysis/SpecialFunctions/Log/Sum.lean`, Terence Tao;
* `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`, `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`,
  `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`, `Mathlib/Topology/DiscreteSubset.lean`,
  `Mathlib/Algebra/Squarefree/Basic.lean`: the authors named in those files.
-/

/-! ### `convert`

The newer Mathlib's `convert` closes an equation between two instances before its congruence step, at the
transparency of instances (`preTransparency := .instances` in `Convert.CheapConfig`); the older one leaves
`Complex.instAddCommMonoid = Complex.addCommGroup.toAddCommMonoid` as a goal, and the cases after it are then one
off. The tactic is declared again here with the newer defaults: an elaborator of a file that imports Mathlib is
tried before Mathlib's. Nothing but the defaults differs between the two versions of `Mathlib/Tactic/Convert.lean`. -/

namespace PortCompat

open Lean Meta Elab Tactic Mathlib.Tactic

/-- `Convert.CheapConfig` of the newer Mathlib. -/
structure ConvertCheap extends Congr!.Config where
  preTransparency := .instances
  postTransparency := .reducible
  sameFun := true

declare_config_elab elabConvertCheap ConvertCheap

/-- `Convert.ExpensiveConfig` of the newer Mathlib. -/
structure ConvertExpensive extends ConvertCheap where
  postTransparency := .default
  sameFun := false

declare_config_elab elabConvertExpensive ConvertExpensive

def elabConvertConfig (expensive : Bool) (stx : Syntax) : TacticM Congr!.Config := do
  if expensive then
    pure { ← elabConvertExpensive stx with }
  else
    pure { ← elabConvertCheap stx with }

elab_rules : tactic
| `(tactic| convert $[!%$expensive]? $cfg $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
  withMainContext do
    let config ← elabConvertConfig expensive.isSome cfg
    let patterns := (ps?.getD #[]).toList
    let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
    let (e, gs) ← elabTermForConvert term expectedType
    liftMetaTactic fun g ↦
      return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs

elab_rules : tactic
| `(tactic| convert_to $[!%$expensive]? $cfg $[←%$sym]? $newType $[using $n]?
    $[with $ps?*]? $[$loc?:location]?) => do
  let n : ℕ := n |>.map (·.getNat) |>.getD 1
  let config ← elabConvertConfig expensive.isSome cfg
  let patterns := (ps?.getD #[]).toList
  withLocation (expandOptLocation (mkOptionalNode loc?))
    (atLocal := fun fvarId ↦ do
      let (e, gs) ← elabTermForConvert newType (← inferType (← fvarId.getType))
      liftMetaTactic fun g ↦ do
        let (g', gs') ← g.convertLocalDecl fvarId e sym.isSome n config patterns
        return (gs' ++ (g' :: gs)))
    (atTarget := do
      let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
      let (e, gs) ← elabTermForConvert (← `((id ?_ : $newType))) expectedType
      liftMetaTactic fun g ↦
        return (← g.convert e sym.isSome n config patterns) ++ gs)
    (failed := fun _ ↦ throwError "convert_to failed")

end PortCompat

/-! ### A check that fails

`#print axioms` prints, and the compiler of the port keeps errors only. `#assert_standard_axioms a b` is an error
unless `a` and `b` depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`: a proof that failed
and was kept as `sorry` shows as `sorryAx`, and a declaration that the kernel refused shows as itself. -/

open Lean Elab Command in
elab "#assert_standard_axioms" ids:(ppSpace ident)+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    for a in ← liftCoreM <| Lean.collectAxioms n do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwErrorAt id "{n} depends on the axiom {a}"

/-! ### The simp set

The 71 lemmas that both versions of Mathlib have and only the newer one marks `@[simp]`, as
`tools/rh/simp_diff.py` lists them from the two simp sets (`tools/rh/lean/DumpSimp.lean`). The 342 that only the
older one marks are in `simp_out.json` beside this file, and `tools/rh/bundle_files.py --simp-out` takes them out
of the simp set of the files it compiles. With both, `simp` on the older Mathlib has the newer simp set, short of
the lemmas that only the newer Mathlib has. -/

attribute [simp] Associates.mk_eq_mk_iff_associated Associates.quot_mk_eq_mk Associates.quotient_mk_eq_mk
  Bool.cond_eq_ite BoundedVariationOn.vectorMeasure_Icc BoundedVariationOn.vectorMeasure_Ici
  BoundedVariationOn.vectorMeasure_Ico BoundedVariationOn.vectorMeasure_Iic
  BoundedVariationOn.vectorMeasure_Iio BoundedVariationOn.vectorMeasure_Ioc
  BoundedVariationOn.vectorMeasure_Ioi BoundedVariationOn.vectorMeasure_Ioo
  BoundedVariationOn.vectorMeasure_singleton BoundedVariationOn.vectorMeasure_univ Cardinal.mk_Iio_lt
  CategoryTheory.Functor.isLimitWeightedLimCone_fac_assoc CategoryTheory.Limits.Pi.lift_π
  CategoryTheory.Limits.WidePushout.arrow_ι_assoc Circle.norm_coe CompleteLatticeHom.apply_liminf_iterate
  ContinuousLinearMap.coe_le_coe_iff DerivedCategory.singleFunctorsPostcompQIso_hom_hom
  DerivedCategory.singleFunctorsPostcompQIso_inv_hom ENNReal.edist_eq_top_iff EReal.natCast_ne_bot
  EReal.natCast_ne_top Finsupp.ofSupportFinite_coe Function.Embedding.coe_trans List.tfae_cons_of_mem
  MulRingNorm.mulRingNormEquivAbsoluteValue_apply MulRingNorm.mulRingNormEquivAbsoluteValue_symm_apply
  Nat.factorization_def Nat.isPowerOfTwo_nextPowerOfTwo Nat.isPowerOfTwo_one Nat.not_isPowerOfTwo_zero
  PresheafOfModules.pushforward_map_app_apply PresheafOfModules.pushforward_obj_map_apply
  PresheafOfModules.toSheafify_app_apply ProbabilityTheory.HasLaw.id RKHS.kerFun_apply Rat.padicValuation_cast
  SSet.yonedaEquiv_symm_app_objEquiv_symm Set.image_insert_eq SkewMonoidAlgebra.mapDomain_single
  SkewMonoidAlgebra.sum_single TensorProduct.congr_symm UniformSpace.Completion.coe_zero
  WeakPseudoEMetricSpace.edist_self WeierstrassCurve.Affine.Point.sym2x_neg_left
  WeierstrassCurve.Affine.Point.sym2x_neg_right WithLp.unitization_nnnorm_inr WithLp.unitization_norm_inr
  birkhoffAverage_one birkhoffAverage_zero birkhoffSum_one birkhoffSum_zero chartAt_self_eq
  exteriorPower.finrank_eq iInf_of_isEmpty iSup_of_empty' le_max_iff lt_max_iff lt_min_iff max_lt_iff
  min_le_iff min_lt_iff not_infIrred_top not_infPrime_top stdSimplex.add_eq_one
attribute [simp↓] Finsupp.mapDomain_id
attribute [simp ←] Submodule.norm_coe

/-! ### Lean: the names that `if_pos`, `if_neg`, `dif_pos` and `dif_neg` have in `v4.35` -/

alias ite_eq_left := if_pos
alias ite_eq_right := if_neg
alias dite_eq_left := dif_pos
alias dite_eq_right := dif_neg

/-! ### Renamed declarations

The newer Lean and Mathlib keep the former name of a renamed declaration as a deprecated alias, so the renames
between the two pins can be read from the newer one (`tools/rh/lean/DumpNames.lean`): 875 declarations that the
older pin has under the former name only. Those whose newer name ends in a word that the files of the port use
are given their newer name here, since a proof may reach them by field notation
(`Complex.isometry_ofReal.antilipschitzWith`). -/

alias AffineIsometry.antilipschitzWith := AffineIsometry.antilipschitz
alias AffineIsometryEquiv.antilipschitzWith := AffineIsometryEquiv.antilipschitz
alias ApproximatesLinearOn.antilipschitzWith := ApproximatesLinearOn.antilipschitz
alias CategoryTheory.Functor.Elements.π := CategoryTheory.CategoryOfElements.π
alias CoalgHom.coe_injective := CoalgHom.coe_fn_injective
alias Complex.HadamardThreeLines.eventuallyLE := Complex.HadamardThreeLines.eventuallyle
alias Dilation.antilipschitzWith := Dilation.antilipschitz
alias Filter.EventuallyEqSet.biUnion := Filter.EventuallyEq.biUnion
alias Filter.EventuallyEqSet.compl := Filter.EventuallyEq.compl
alias Filter.EventuallyEqSet.diff := Filter.EventuallyEq.diff
alias Filter.EventuallyEqSet.inter := Filter.EventuallyEq.inter
alias Filter.EventuallyEqSet.union := Filter.EventuallyEq.union
alias Filter.EventuallySubset.biUnion := Filter.EventuallyLE.biUnion
alias Filter.EventuallySubset.compl := Filter.EventuallyLE.compl
alias Filter.EventuallySubset.diff := Filter.EventuallyLE.diff
alias Filter.EventuallySubset.inter := Filter.EventuallyLE.inter
alias Filter.EventuallySubset.union := Filter.EventuallyLE.union
alias IsExtrOn.preimage := IsExtrOn.on_preimage
alias IsLocalExtrOn.mono := IsLocalExtrOn.on_subset
alias IsLocalMaxOn.mono := IsLocalMaxOn.on_subset
alias IsLocalMinOn.mono := IsLocalMinOn.on_subset
alias IsMaxOn.preimage := IsMaxOn.on_preimage
alias IsMinOn.preimage := IsMinOn.on_preimage
alias IsSMulRegular.all := isSMulRegular_of_group
alias Isometry.antilipschitzWith := Isometry.antilipschitz
alias IsometryClass.antilipschitzWith := IsometryClass.antilipschitz
alias LinearIsometry.antilipschitzWith := LinearIsometry.antilipschitz
alias LinearIsometryEquiv.antilipschitzWith := LinearIsometryEquiv.antilipschitz
alias List.Forall₂.prod_le_prod := List.Forall₂.prod_le_prod'
alias List.Sublist.prod_le_prod := List.Sublist.prod_le_prod'
alias List.SublistForall₂.prod_le_prod := List.SublistForall₂.prod_le_prod'
alias List.prod_le_prod := List.prod_le_prod'
alias MeasureTheory.MemLp.fun_mul := MeasureTheory.MemLp.mul'
alias PadicInt.norm_coe := PadicInt.padic_norm_e_of_padicInt
alias SemilinearIsometryClass.antilipschitzWith := SemilinearIsometryClass.antilipschitz
alias Subgroup.Commensurable.smul := Subgroup.Commensurable.conj
alias TopologicalSpace.NonemptyCompacts.dist_eq := Metric.NonemptyCompacts.dist_eq
alias balancedCore.balanced := balancedCore_balanced

/-! ### Products in an ordered monoid with zero

In the newer Mathlib `Finset.prod_le_prod` is the statement for an ordered monoid, which the older one calls
`Finset.prod_le_prod'`, and the statement with nonnegative factors has the name with `₀`. A use of the unmarked name
in the library therefore means another statement here, and is changed where it is used. -/

alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod

/-! ### Logarithmic derivatives

The older `logDeriv_mul` and `logDeriv_prod` are about `fun z => f z * g z`; the newer ones are about `f * g`, and
the statements about the functions written out have the names with `fun`. -/

alias logDeriv_fun_mul := logDeriv_mul
alias logDeriv_fun_div := logDeriv_div
alias logDeriv_fun_prod := logDeriv_prod

/-! ### The arctangent -/

namespace Real

theorem arctan_lt_self {x : ℝ} (h : 0 < x) : arctan x < x := by
  simpa using lt_tan (arctan_pos.2 h) (arctan_lt_pi_div_two x)

theorem arctan_le_self {x : ℝ} (h : 0 ≤ x) : arctan x ≤ x := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · exact (arctan_lt_self h).le

end Real

/-! ### The digamma function -/

namespace Complex

theorem digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h ↦
      hs (m + n) (by push_cast at h ⊢; linear_combination h)
    rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
      digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]
    ring

theorem digamma_nat_add_one (n : ℕ) :
    digamma (n + 1) = harmonic n - Real.eulerMascheroniConstant := by
  have h1 : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [add_comm _ 1, digamma_apply_add_nat h1 n, digamma_one, harmonic]
  push_cast [add_comm (1 : ℂ)]
  ring

/-- If `g` has derivative `a` at `s`, then the logarithmic derivative of `Gamma ∘ g` at `s` is
`a * digamma (g s)`. -/
theorem _root_.HasDerivAt.logDeriv_Gamma {g : ℂ → ℂ} {a s : ℂ} (hg : HasDerivAt g a s)
    (h : ∀ m : ℕ, g s ≠ -(m : ℂ)) :
    logDeriv (fun z ↦ Gamma (g z)) s = a * digamma (g s) := by
  rw [show (fun z ↦ Gamma (g z)) = Gamma ∘ g from rfl,
    logDeriv_comp (differentiableAt_Gamma _ h) hg.differentiableAt, hg.deriv, digamma_def]
  exact mul_comm _ _

open scoped Real in
/-- **Euler's reflection formula for the digamma function**:
`ψ (1 - s) = ψ s + π * cot (π * s)` for `s` not an integer. -/
theorem digamma_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    digamma (1 - s) = digamma s + π * cot (π * s) := by
  have h1 (m : ℕ) : s ≠ -m := by simpa using hs (-m)
  have h2 (m : ℕ) : 1 - s ≠ -m := fun h ↦ hs (1 + m) (by push_cast; linear_combination -h)
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsin : sin (π * s) ≠ 0 := by
    rw [Ne, sin_eq_zero_iff]
    rintro ⟨n, hn⟩
    refine hs n ?_
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  -- the logarithmic derivative of `Γ(s) Γ(1 - s) = π / sin (π s)`
  have key := congr(logDeriv $(funext Gamma_mul_Gamma_one_sub) s)
  rw [logDeriv_fun_mul (f := Gamma) (g := fun z => Gamma (1 - z)) s (Gamma_ne_zero h1) (Gamma_ne_zero h2)
      (differentiableAt_Gamma _ h1) ((differentiableAt_Gamma _ h2).comp s (by fun_prop)),
    ((hasDerivAt_id' s).const_sub 1).logDeriv_Gamma h2, ← digamma_def] at key
  have hd : HasDerivAt (fun z : ℂ => (π : ℂ) / sin (π * z))
      (-(π * (cos (π * s) * π)) / sin (π * s) ^ 2) s := by
    have h := ((hasDerivAt_id' s).const_mul (π : ℂ)).csin
    have := (hasDerivAt_const s (π : ℂ)).div h hsin
    convert this using 1
    ring
  rw [logDeriv_apply, hd.deriv] at key
  have hR : -(↑π * (cos (↑π * s) * ↑π)) / sin (↑π * s) ^ 2 / (↑π / sin (↑π * s))
      = -(↑π * (cos (↑π * s) / sin (↑π * s))) := by
    field_simp
  rw [hR] at key
  rw [cot_eq_cos_div_sin]
  linear_combination -key

theorem digamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ)) :
    digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2 := by
  have hs₀ (m : ℕ) : s ≠ -(m : ℂ) := fun h ↦
    hs (2 * m) (by push_cast; linear_combination 2 * h)
  have hs₁ (m : ℕ) : s + 1 / 2 ≠ -(m : ℂ) := fun h ↦
    hs (2 * m + 1) (by push_cast; linear_combination 2 * h)
  have hpow : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by simp [cpow_eq_zero_iff]
  have hd2 := hasDerivAt_id' s |>.const_mul 2 |>.const_sub 1 |>.const_cpow <|
    .inl (by norm_num : (2 : ℂ) ≠ 0)
  have hpi : ((√Real.pi : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 Real.pi_pos)
  -- take logarithmic derivatives of Legendre's formula `Γ(s) Γ(s + 1/2) = Γ(2s) 2^(1-2s) √π`
  suffices key : digamma s + digamma (s + 1 / 2) = 2 * digamma (2 * s) - 2 * log 2 by
    linear_combination (-1 / 2 : ℂ) * key
  calc
    digamma s + digamma (s + 1 / 2) = logDeriv (fun z ↦ Gamma z * Gamma (z + 1 / 2)) s := by
      rw [logDeriv_fun_mul (g := fun z ↦ Gamma (z + 1 / 2)) s (Gamma_ne_zero hs₀)
        (Gamma_ne_zero hs₁) (differentiableAt_Gamma _ hs₀)
        ((differentiableAt_Gamma _ hs₁).comp s (by fun_prop)),
        ((hasDerivAt_id' s).add_const (1 / 2)).logDeriv_Gamma hs₁, ← digamma_def]
      ring
    _ = logDeriv (fun z ↦ Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * ((√Real.pi : ℝ) : ℂ)) s := by
      rw [funext Gamma_mul_Gamma_add_half]
    _ = 2 * digamma (2 * s) - 2 * log 2 := by
      rw [logDeriv_mul_const s ((√Real.pi : ℝ) : ℂ) hpi,
        logDeriv_fun_mul (f := fun z ↦ Gamma (2 * z)) s
          (Gamma_ne_zero hs) hpow ((differentiableAt_Gamma _ hs).comp s (by fun_prop))
          hd2.differentiableAt,
        ((hasDerivAt_id' s).const_mul 2).logDeriv_Gamma hs, mul_one, sub_eq_add_neg]
      congr! 1
      rw [logDeriv_apply, hd2.deriv, div_eq_iff hpow]
      ring

end Complex

/-! ### Partial sums of the logarithm -/

namespace Real

open Finset in
/-- The partial sum of the logarithm is equal to the log of the factorial. -/
theorem sum_log_eq_log_factorial (N : ℕ) : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le N),
      Finset.sum_insert (by simp), ih, Nat.factorial_succ]
    push_cast
    rw [log_mul (by positivity) (by positivity)]

open Finset intervalIntegral MeasureTheory in
/-- A crude upper bound on the partial sum of the logarithm. -/
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have aux1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have aux2 : 1 ≤ ⌊x⌋₊ := by simpa
  have aux3 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast aux2
  have hmono : MonotoneOn log (Set.Icc ((1 : ℕ) : ℝ) (⌊x⌋₊ : ℝ)) :=
    strictMonoOn_log.monotoneOn.mono fun y hy => by
      have : (1 : ℝ) ≤ y := by simpa using hy.1
      exact Set.mem_Ioi.2 (by linarith)
  have hsum : ∑ n ∈ Ico 1 ⌊x⌋₊, log (n : ℝ) ≤ ∫ t in ((1 : ℕ) : ℝ)..(⌊x⌋₊ : ℝ), log t :=
    hmono.sum_le_integral_Ico aux2
  have hsplit : ∑ n ∈ Ioc 0 ⌊x⌋₊, log (n : ℝ) = ∑ n ∈ Ico 1 ⌊x⌋₊, log (n : ℝ) + log (⌊x⌋₊ : ℝ) := by
    have h : Ioc 0 ⌊x⌋₊ = insert ⌊x⌋₊ (Ico 1 ⌊x⌋₊) := by
      ext n
      simp only [mem_Ioc, mem_insert, mem_Ico]
      omega
    rw [h, Finset.sum_insert (by simp), add_comm]
  have hlast : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log (by linarith) aux1
  have hint : ∫ t in ((1 : ℕ) : ℝ)..(⌊x⌋₊ : ℝ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    rw [integral_log, Nat.cast_one, log_one]
    ring
  have hfun : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    -- `t ↦ t log t - t` is monotone on `[1, ∞)`: its derivative is `log t`
    have hderiv : ∀ t ∈ Set.Icc (⌊x⌋₊ : ℝ) x, HasDerivAt (fun t : ℝ => t * log t - t) (log t) t := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have h : HasDerivAt (fun t : ℝ => t * log t - t) (1 * log t + t * t⁻¹ - 1) t :=
        ((hasDerivAt_id' t).mul (hasDerivAt_log ht0)).sub (hasDerivAt_id' t)
      convert h using 1
      rw [one_mul, mul_inv_cancel₀ ht0, add_sub_cancel_right]
    have hmon : MonotoneOn (fun t : ℝ => t * log t - t) (Set.Icc (⌊x⌋₊ : ℝ) x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
        (fun t ht => ?_)
      rw [(hderiv t (interior_subset ht)).deriv]
      exact log_nonneg (by linarith [(interior_subset ht : t ∈ Set.Icc (⌊x⌋₊ : ℝ) x).1])
    exact hmon (Set.left_mem_Icc.2 aux1) (Set.right_mem_Icc.2 aux1) aux1
  rw [hsplit]
  linarith

/-- A sharper bound on the partial sum of the logarithm in the natural number case. -/
theorem le_sum_log_nat (N : ℕ) : N * log N - N ≤ ∑ n ∈ Finset.Ioc 0 N, log n := by
  by_cases hN : N = 0
  · simp [hN]
  have h1 : 0 ≤ log N := log_natCast_nonneg N
  have h2 : 0 ≤ log (2 * Real.pi) := log_nonneg (by linarith [two_le_pi])
  have h3 := Stirling.le_log_factorial_stirling hN
  rw [sum_log_eq_log_factorial]
  linarith

end Real

/-! ### The substitution `y = exp x` -/

namespace MeasureTheory

open Set Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Substitution `y = exp x` in integrals over the whole line. -/
theorem integral_comp_exp (g : ℝ → E) :
    ∫ x, exp x • g (exp x) = ∫ y in Ioi 0, g y := by
  symm
  rw [← range_exp, ← image_univ]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

theorem integrable_comp_exp (g : ℝ → E) :
    Integrable (fun x ↦ exp x • g (exp x)) ↔ IntegrableOn g (Ioi 0) := by
  rw [← integrableOn_univ, ← range_exp, ← image_univ]
  symm
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

end MeasureTheory

/-! ### Other statements -/

open scoped ContDiff in
/-- The iterated derivatives up to order `m` of a smooth compactly supported function are
uniformly bounded. -/
lemma HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  refine (hA i y).trans (le_trans ?_ (le_max_right _ _))
  exact Finset.le_sup' A (Finset.mem_range.2 (by omega))

theorem integrable_inv_one_add_mul_sq {b : ℝ} (hb : b ≠ 0) :
    MeasureTheory.Integrable fun x : ℝ ↦ (1 + (b * x) ^ 2)⁻¹ :=
  (integrable_inv_one_add_sq.comp_mul_left' hb).congr (by simp)

/-- A set `S` is codiscrete within `T` iff it is a punctured neighborhood within `T` of every
point of `T`. -/
theorem mem_codiscreteWithin_iff_forall_mem_nhdsWithin {X : Type*} [TopologicalSpace X] {S T : Set X} :
    S ∈ Filter.codiscreteWithin T ↔ ∀ x ∈ T, S ∈ nhdsWithin x (T \ {x}) := by
  simp [Filter.codiscreteWithin]

/-- Every element of a unique factorization monoid is a square times a squarefree element. -/
theorem exists_sq_mul_squarefree {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R] (x : R) :
    ∃ e d : R, e ^ 2 * d = x ∧ Squarefree d := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => exact ⟨0, 1, by simp, squarefree_one⟩
  | unit u hu => exact ⟨1, u, by simp, hu.squarefree⟩
  | mul z p hz hp ih =>
    obtain ⟨e, d, rfl, hd⟩ := ih
    by_cases hpd : p ∣ d
    · obtain ⟨d', rfl⟩ := hpd
      exact ⟨e * p, d', by simp only [pow_two]; ac_rfl, hd.of_mul_right⟩
    · refine ⟨e, d * p, by ac_rfl, ?_⟩
      rw [squarefree_mul_iff]
      exact ⟨(hp.isRelPrime_iff_not_dvd.mpr hpd).symm, hd, hp.squarefree⟩

/-! ### Temperate growth -/

@[fun_prop]
theorem Real.hasTemperateGrowth_sin : Real.sin.HasTemperateGrowth := by
  refine ⟨Real.contDiff_sin, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_sin_le_one n x

@[fun_prop]
theorem Real.hasTemperateGrowth_cos : Real.cos.HasTemperateGrowth := by
  refine ⟨Real.contDiff_cos, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_cos_le_one n x

@[fun_prop]
theorem Complex.hasTemperateGrowth_ofReal : Complex.ofReal.HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth

@[fun_prop]
theorem Complex.hasTemperateGrowth_re : Complex.re.HasTemperateGrowth :=
  Complex.reCLM.hasTemperateGrowth

@[fun_prop]
theorem Complex.hasTemperateGrowth_im : Complex.im.HasTemperateGrowth :=
  Complex.imCLM.hasTemperateGrowth

/-- The function `x ↦ exp (x * I)` has temperate growth. -/
@[fun_prop]
theorem Complex.hasTemperateGrowth_exp_mul_I :
    (fun x : ℝ ↦ Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  simp only [Complex.exp_ofReal_mul_I]
  exact (Complex.hasTemperateGrowth_ofReal.comp Real.hasTemperateGrowth_cos).add
    ((Complex.hasTemperateGrowth_ofReal.comp Real.hasTemperateGrowth_sin).mul
      (Function.HasTemperateGrowth.const Complex.I))

/-! ### Sums and integrals of monotone functions -/

open MeasureTheory Set in
theorem AntitoneOn.sum_le_integral_of_integrableOn {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ioc x₀ (x₀ + a))) (hfi : IntegrableOn f (Icc x₀ (x₀ + a))) :
    ∑ i ∈ Finset.range a, f (x₀ + ↑(i + 1)) ≤ ∫ x in x₀..x₀ + a, f x := by
  have hint : ∀ k < a, IntervalIntegrable f volume (x₀ + (k : ℕ)) (x₀ + ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast hk
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le (by push_cast; linarith)).2 (hfi.mono_set ?_)
    exact Icc_subset_Icc (by simp) (by linarith)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => x₀ + (k : ℝ)) hint
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < a := Finset.mem_range.1 hi
  have hi'' : ((i + 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast hi'
  have hle : x₀ + (i : ℝ) ≤ x₀ + ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
  rw [intervalIntegral.integral_of_le hle]
  have hvol : volume.real (Ioc (x₀ + (i : ℝ)) (x₀ + ((i + 1 : ℕ) : ℝ))) = 1 := by
    rw [Measure.real, Real.volume_Ioc]; push_cast; simp
  calc f (x₀ + ((i + 1 : ℕ) : ℝ))
      = ∫ _ in Ioc (x₀ + (i : ℝ)) (x₀ + ((i + 1 : ℕ) : ℝ)), f (x₀ + ((i + 1 : ℕ) : ℝ)) := by
        rw [setIntegral_const, hvol, one_smul]
    _ ≤ ∫ x in Ioc (x₀ + (i : ℝ)) (x₀ + ((i + 1 : ℕ) : ℝ)), f x := by
        refine setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          ((hint i hi').1) measurableSet_Ioc fun x hx => ?_
        have hx0 : x₀ < x := by have := hx.1; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
        exact hf ⟨hx0, by linarith [hx.2]⟩ ⟨by push_cast; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith,
          by linarith⟩ hx.2

open MeasureTheory Set in
theorem MonotoneOn.integral_le_sum_of_integrableOn {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ioc x₀ (x₀ + a))) (hfi : IntegrableOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x ≤ ∑ i ∈ Finset.range a, f (x₀ + ↑(i + 1)) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_of_integrableOn hfi.neg
