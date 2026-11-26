import GlRep

/-!
# Isotypic projectors with bounded denominators, and Kostant integrality

For a representation `G` of `gl_n` over `ℚ_p` (`GlRep`), a finite-dimensional stable subspace `W` whose weights have
spread `≤ l` (`μ a − μ b ≤ l`), and an additive subgroup `M` closed under `ℤ_p`-scalars (`ZpClosed`), the divided powers
`E a b ^ k / k!` (`a ≠ b`, `DPStable`) and the weight projections (`CompStable`), this file bounds the denominators of
the projectors of `GlRep` on `M`, with the projector exponent `projExp p n l = C(n, 2)·⌊log_p(l + n − 1)⌋`.

The coefficients `1 / C(N + k, k)` of the rank-one factors have `p`-adic valuation `≤ ⌊log_p(N + k)⌋`
(`exists_padicInt_ecoef`, Kummer), and every nonzero term of a factor of the extremal projector has `N + k ≤ l + n − 1`;
so the extremal projector at a dominant weight loses `p^(projExp p n l)` (`hwProj_int`: T5 with the bound of T6). The
isotypic projector is `d` times the average `Π₀(hwOp λ)` (`GlRep.isoAvg_spec`), an extremal projector at weight `0` on
`End W` (whose divided powers are `Σ ± e^(i) T e^(k−i)`, `endRep_dpow`) applied to the highest weight projector; on the
lattice of operators mapping `M ∩ W` into the Kostant span `N` of the integral highest weight vectors (`opLat`) it loses
another `p^(projExp p n l)` (`endRep_string`: the root strings at weight `0` have length `≤ l`). Hence `p^(2·projExp p n
l)·Q_λ(M ∩ W) ⊆ N ⊆ M` (`isoKostant_int`, `isoProj_int`), Kostant integrality for isotypic vectors (`kostant_int`), and
the same bound for every type projector (`typeProj_int`, a finite sum of isotypic ones).
-/

open Finset

noncomputable section

namespace GlRep

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The projector exponent** `C(n, 2)·⌊log_p(l + n − 1)⌋`. -/
def projExp (p n l : ℕ) : ℕ := n.choose 2 * Nat.log p (l + n - 1)

/-- **`p^δ / C(N + k, k)` is a `p`-adic integer** once `⌊log_p(N + k)⌋ ≤ δ` (Kummer). -/
theorem exists_padicInt_ecoef (N k δ : ℕ) (h : Nat.log p (N + k) ≤ δ) :
    ∃ z : ℤ_[p], (z : ℚ_[p]) = (p : ℚ_[p]) ^ δ * ecoef N k := by
  have hC : (N + k).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  obtain ⟨v, u, hpu, hCu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hC p hp.out.one_lt.ne'
  have hv : v ≤ δ := by
    have h1 : ((N + k).choose k).factorization p = v := by
      have hu0 : u ≠ 0 := by rintro rfl; exact hpu (dvd_zero p)
      rw [hCu, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hu0,
        Finsupp.add_apply, Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpu, add_zero]
    have := (Nat.factorization_choose_le_log (p := p) (n := N + k) (k := k))
    omega
  have hu : IsUnit (u : ℤ_[p]) := PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpu))
  refine ⟨(-1) ^ k * (p : ℤ_[p]) ^ (δ - v) * ↑hu.unit⁻¹, ?_⟩
  have hu' : (u : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hpu (dvd_zero p))
  have hinv : ((↑hu.unit⁻¹ : ℤ_[p]) : ℚ_[p]) = ((u : ℚ_[p]))⁻¹ := by
    have key := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hu.val_inv_mul
    simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at key
    exact eq_inv_of_mul_eq_one_left key
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_neg, PadicInt.coe_one, PadicInt.coe_natCast, hinv,
    ecoef, hCu, Nat.cast_mul, Nat.cast_pow]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [show δ = (δ - v) + v by omega, pow_add]
  field_simp
  rw [Nat.sub_add_cancel hv]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ} (G : GlRep ℚ_[p] V n)

/-- **`ℤ_p`-closed subgroups**: closed under multiplication by `p`-adic integers. -/
def ZpClosed (M : AddSubgroup V) : Prop := ∀ (z : ℤ_[p]), ∀ x ∈ M, (z : ℚ_[p]) • x ∈ M

/-- **Divided-power stable** subgroups: stable under `E a b ^ k / k!`, `a ≠ b`. -/
def DPStable (M : AddSubgroup V) : Prop := ∀ a b, a ≠ b → ∀ k, ∀ x ∈ M, dpow (G.E a b) k x ∈ M

/-- **Comp-stable** subgroups: stable under the weight projections. -/
def CompStable (M : AddSubgroup V) : Prop := ∀ μ, ∀ x ∈ M, G.comp μ x ∈ M

theorem zpClosed_smul {M : AddSubgroup V} (hM : ZpClosed (p := p) M) {c : ℚ_[p]} {z : ℤ_[p]}
    (hz : (z : ℚ_[p]) = c) {x : V} (hx : x ∈ M) : c • x ∈ M := hz ▸ hM z x hx

/-- **The rank-one factor loses `p^δ`** on a divided-power stable subgroup, when every nonzero term has
`⌊log_p(N + k)⌋ ≤ δ`. -/
theorem pfac_int {M : AddSubgroup V} (hZ : ZpClosed (p := p) M) (hM : G.DPStable M) {a b : Fin n} (hab : a ≠ b)
    (N D δ : ℕ) {y : V} (hyM : y ∈ M) (hδ : ∀ k, dpow (G.E a b) k y ≠ 0 → Nat.log p (N + k) ≤ δ) :
    (p : ℚ_[p]) ^ δ • G.pfac a b N D y ∈ M := by
  simp only [pfac, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul, Module.End.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  by_cases hk : dpow (G.E a b) k y = 0
  · rw [hk, map_zero, smul_zero]; exact zero_mem _
  obtain ⟨z, hz⟩ := exists_padicInt_ecoef (p := p) N k δ (hδ k hk)
  exact zpClosed_smul hZ hz (hM b a hab.symm k _ (hM a b hab k y hyM))

/-- **The string bound from the spread**: on `W` with weights of spread `≤ L`, a nonzero `e^(k) z` (`z` of weight `μ`)
has `μ a − μ b + k ≤ L`. -/
theorem string_bound {W : Submodule ℚ_[p] V} (hW : G.Stable W) {L : ℕ}
    (hL : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ L) {a b : Fin n} (hab : a ≠ b) {μ : Fin n → ℤ} {z : V}
    (hz : G.IsWt μ z) (hzW : z ∈ W) (k : ℕ) (hk : dpow (G.E a b) k z ≠ 0) : μ a - μ b + k ≤ L := by
  have h1 := hL _ (G.mem_wts_of_isWt (hW.dpow_mem a b k hzW) (hz.dpow a b k) hk) a b
  simp only [Pi.add_apply, Pi.smul_apply, rt_apply_left hab, rt_apply_right hab, smul_eq_mul] at h1
  linarith

theorem rfac_int {W : Submodule ℚ_[p] V} (hW : G.Stable W) {M : AddSubgroup V} (hZ : ZpClosed (p := p) M)
    (hM : G.DPStable M) {L : ℕ} (a : Fin n) (μ : Fin n → ℤ) (D : ℕ)
    (hL : ∀ z ∈ W, G.IsWt μ z → ∀ a b, a < b → ∀ k, dpow (G.E a b) k z ≠ 0 → μ a - μ b + k ≤ L) :
    ∀ (bs : List (Fin n)) (t : ℕ), (a :: bs).Pairwise (· < ·) → (∀ b ∈ bs, μ b ≤ μ a) → t + bs.length ≤ n →
      ∀ y ∈ W, G.IsWt μ y → y ∈ M →
        (p : ℚ_[p]) ^ (bs.length * Nat.log p (L + n - 1)) • G.rfac a μ D bs t y ∈ M := by
  intro bs
  induction bs with
  | nil => intro t _ _ _ y _ _ hyM; simpa [rfac] using hyM
  | cons b bs ih =>
    intro t hsort hdom htn y hyW hy hyM
    have hsort' : (a :: bs).Pairwise (· < ·) := by
      simp only [List.pairwise_cons, List.mem_cons] at hsort ⊢
      exact ⟨fun x hx => hsort.1 x (Or.inr hx), hsort.2.2⟩
    have hab : a < b := List.rel_of_pairwise_cons hsort List.mem_cons_self
    have h1 := ih (t + 1) hsort' (fun c hc => hdom c (List.mem_cons_of_mem b hc))
      (by simp only [List.length_cons] at htn; omega) y hyW hy hyM
    set Y := (p : ℚ_[p]) ^ (bs.length * Nat.log p (L + n - 1)) • G.rfac a μ D bs (t + 1) y
    have hYW : Y ∈ W := W.smul_mem _ (G.rfac_mem hW _ _ _ _ _ hyW)
    have hYw : G.IsWt μ Y := (G.isWt_rfac hy _ _ _ _).smul _
    have h2 := G.pfac_int hZ hM (ne_of_lt hab) ((μ a - μ b).toNat + t) D (Nat.log p (L + n - 1)) h1
      (fun k hk => by
        refine Nat.log_mono_right ?_
        have := hL Y hYW hYw a b hab k hk
        have hd := hdom b List.mem_cons_self
        simp only [List.length_cons] at htn
        omega)
    rw [rfac, Module.End.mul_apply, List.length_cons, add_mul, one_mul, add_comm, pow_add, ← smul_smul,
      ← map_smul]
    exact h2

/-- **The extremal projector loses `p^(C(|l|, 2)·⌊log_p(L + n − 1)⌋)`** on a divided-power stable subgroup (`L` a
string bound on `W`). -/
theorem xproj_int {W : Submodule ℚ_[p] V} (hW : G.Stable W) {M : AddSubgroup V} (hZ : ZpClosed (p := p) M)
    (hM : G.DPStable M) {L : ℕ} (μ : Fin n → ℤ) (D : ℕ)
    (hL : ∀ z ∈ W, G.IsWt μ z → ∀ a b, a < b → ∀ k, dpow (G.E a b) k z ≠ 0 → μ a - μ b + k ≤ L) :
    ∀ (l : List (Fin n)), l.Pairwise (· < ·) → (∀ a ∈ l, ∀ b ∈ l, a < b → μ b ≤ μ a) → l.length ≤ n →
      ∀ y ∈ W, G.IsWt μ y → y ∈ M →
        (p : ℚ_[p]) ^ (l.length.choose 2 * Nat.log p (L + n - 1)) • G.xproj μ D l y ∈ M := by
  intro l
  induction l with
  | nil => intro _ _ _ y _ _ hyM; simpa [xproj] using hyM
  | cons a l ih =>
    intro hsort hdom hln y hyW hy hyM
    have h1 := ih (List.Pairwise.of_cons hsort)
      (fun x hx z hz => hdom x (List.mem_cons_of_mem a hx) z (List.mem_cons_of_mem a hz))
      (by simp only [List.length_cons] at hln; omega) y hyW hy hyM
    have h2 := G.rfac_int hW hZ hM a μ D hL l 1 hsort
      (fun b hb => hdom a List.mem_cons_self b (List.mem_cons_of_mem a hb)
        (List.rel_of_pairwise_cons hsort hb))
      (by simp only [List.length_cons] at hln; omega) _ (W.smul_mem _ (G.xproj_mem hW _ _ _ hyW))
      ((G.isWt_xproj hy _ _).smul _) h1
    rw [xproj, Module.End.mul_apply, List.length_cons, Nat.choose_succ_succ', Nat.choose_one_right, add_mul,
      pow_add, ← smul_smul, ← map_smul]
    exact h2

/-- **The highest weight projector (T5 with T6's bound)**: for `μ` dominant, `p^(projExp p n L)·xproj μ` maps the
weight-`μ` vectors of `M ∩ W` into `M`, and onto highest weight vectors of weight `μ`. -/
theorem hwProj_int {W : Submodule ℚ_[p] V} (hW : G.Stable W) {M : AddSubgroup V} (hZ : ZpClosed (p := p) M)
    (hM : G.DPStable M) {L : ℕ} (hL : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ L) {μ : Fin n → ℤ} (hμ : Antitone μ)
    (D : ℕ) {y : V} (hyW : y ∈ W) (hy : G.IsWt μ y) (hyM : y ∈ M) :
    (p : ℚ_[p]) ^ projExp p n L • G.xproj μ D (List.finRange n) y ∈ M := by
  have := G.xproj_int hW hZ hM μ D (fun z hz hμ' a b hab k hk => G.string_bound hW hL (ne_of_lt hab) hμ' hz k hk)
    (List.finRange n) (List.pairwise_lt_finRange n) (fun a _ b _ hab => hμ hab.le) (by simp) y hyW hy hyM
  simpa [projExp] using this

/-! ## Divided powers of the adjoint action -/

section AdDpow

variable {K U : Type*} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]

/-- **Divided powers of the adjoint action**: `(ad e)^(k) T = Σ_i (−1)^(k−i) e^(i) T e^(k−i)`. -/
theorem endRep_dpow (G' : GlRep K U n) (a b : Fin n) (k : ℕ) (T : Module.End K U) :
    dpow (G'.endRep.E a b) k T =
      ∑ i ∈ range (k + 1), ((-1 : K) ^ (k - i)) • (dpow (G'.E a b) i * T * dpow (G'.E a b) (k - i)) := by
  set L := LinearMap.mulLeft K (G'.E a b)
  set R := LinearMap.mulRight K (G'.E a b)
  have hE : G'.endRep.E a b = L + (-1 : K) • R := by
    ext1 T; simp [L, R, endRep_E, sub_eq_add_neg]
  have hc : Commute L ((-1 : K) • R) := (LinearMap.commute_mulLeft_right (R := K) (A := Module.End K U)
    (G'.E a b) (G'.E a b)).smul_right (-1 : K)
  rw [dpow, hE, hc.add_pow, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have key : (L ^ i * ((-1 : K) • R) ^ (k - i) * ((k.choose i : ℕ) : Module.End K (Module.End K U))) T =
      ((-1 : K) ^ (k - i) * (k.choose i : K)) • (G'.E a b ^ i * T * G'.E a b ^ (k - i)) := by
    rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp [Module.End.mul_apply, mul_assoc, mul_comm]
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K, mul_smul_comm, smul_smul]
    congr 1; ring
  rw [key, smul_smul]
  simp only [dpow, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  congr 1
  have h1 := Nat.choose_mul_factorial_mul_factorial hik
  have hf1 : ((i.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hf2 : (((k - i).factorial : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - i)
  have hC : ((k.choose i : ℕ) : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hik).ne'
  rw [← h1]; push_cast
  field_simp

end AdDpow

/-! ## Kostant spans and the integrality of isotypic projectors -/

theorem comp_dpow (μ : Fin n → ℤ) (a b : Fin n) (k : ℕ) (v : V) :
    G.comp μ (dpow (G.E a b) k v) = dpow (G.E a b) k (G.comp (μ - (k : ℤ) • rt a b) v) := by
  simp only [dpow, LinearMap.smul_apply, map_smul]
  congr 1
  induction k generalizing μ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ_apply, comp_E_apply, ih, ← pow_succ_apply]
    congr 2; push_cast; rw [add_smul, one_smul]; abel_nf

/-- **The Kostant span** of a set: the least `ℤ_p`-closed, divided-power stable subgroup containing it. -/
def kostantSpan (S : Set V) : AddSubgroup V := sInf {N | S ⊆ N ∧ ZpClosed (p := p) N ∧ G.DPStable N}

theorem subset_kostantSpan (S : Set V) : S ⊆ G.kostantSpan S := fun x hx => by
  simp only [kostantSpan, SetLike.mem_coe, AddSubgroup.mem_sInf, Set.mem_ofPred_eq]
  exact fun N hN => hN.1 hx

theorem kostantSpan_le {S : Set V} {N : AddSubgroup V} (hS : S ⊆ N) (hZ : ZpClosed (p := p) N)
    (hN : G.DPStable N) : G.kostantSpan S ≤ N := sInf_le ⟨hS, hZ, hN⟩

theorem kostantSpan_zp (S : Set V) : ZpClosed (p := p) (G.kostantSpan S) := fun z x hx => by
  simp only [kostantSpan, AddSubgroup.mem_sInf, Set.mem_ofPred_eq] at hx ⊢
  exact fun N hN => hN.2.1 z x (hx N hN)

theorem kostantSpan_dp (S : Set V) : G.DPStable (G.kostantSpan S) := fun a b hab k x hx => by
  simp only [kostantSpan, AddSubgroup.mem_sInf, Set.mem_ofPred_eq] at hx ⊢
  exact fun N hN => hN.2.2 a b hab k x (hx N hN)

/-- **The Kostant span of weight vectors is stable under the weight projections.** -/
theorem kostantSpan_comp {S : Set V} (hS : ∀ s ∈ S, ∃ μ, G.IsWt μ s) : G.CompStable (G.kostantSpan S) := by
  let N : AddSubgroup V :=
    { carrier := {v | v ∈ G.kostantSpan S ∧ ∀ μ, G.comp μ v ∈ G.kostantSpan S}
      add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun μ => by rw [map_add]; exact add_mem (hx.2 μ) (hy.2 μ)⟩
      zero_mem' := ⟨zero_mem _, fun μ => by rw [map_zero]; exact zero_mem _⟩
      neg_mem' := fun hx => ⟨neg_mem hx.1, fun μ => by rw [map_neg]; exact neg_mem (hx.2 μ)⟩ }
  have hle : G.kostantSpan S ≤ N := by
    refine G.kostantSpan_le (fun s hs => ⟨G.subset_kostantSpan S hs, fun μ => ?_⟩) (fun z x hx => ⟨
      G.kostantSpan_zp S z x hx.1, fun μ => by rw [map_smul]; exact G.kostantSpan_zp S z _ (hx.2 μ)⟩)
      (fun a b hab k x hx => ⟨G.kostantSpan_dp S a b hab k x hx.1, fun μ => by
        rw [comp_dpow]; exact G.kostantSpan_dp S a b hab k _ (hx.2 _)⟩)
    obtain ⟨ν, hν⟩ := hS s hs
    rw [G.comp_of_isWt hν]
    split_ifs
    · exact G.subset_kostantSpan S hs
    · exact zero_mem _
  exact fun μ x hx => (hle hx).2 μ

section OpLat

variable {W : Submodule ℚ_[p] V} [FiniteDimensional ℚ_[p] W] (hW : G.Stable W)

omit [FiniteDimensional ℚ_[p] W] in
theorem coe_dpow_restr (a b : Fin n) (k : ℕ) (y : W) :
    ((dpow ((G.restr hW).E a b) k y : W) : V) = dpow (G.E a b) k (y : V) := by
  simp only [dpow, LinearMap.smul_apply, Submodule.coe_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ_apply, pow_succ_apply, restr_E, ih]

/-- **The operator lattice**: operators of `W` mapping `M ∩ W` into `N`. -/
def opLat (M N : AddSubgroup V) : AddSubgroup (Module.End ℚ_[p] W) where
  carrier := {T | ∀ x : W, (x : V) ∈ M → (T x : V) ∈ N}
  add_mem' hT hT' x hx := by simpa using add_mem (hT x hx) (hT' x hx)
  zero_mem' x _ := by simp
  neg_mem' hT x hx := by simpa using neg_mem (hT x hx)

omit [FiniteDimensional ℚ_[p] W] in
theorem opLat_zp (M : AddSubgroup V) {N : AddSubgroup V} (hN : ZpClosed (p := p) N) :
    ZpClosed (p := p) (opLat (W := W) M N) := fun z T hT x hx => by
  simpa using hN z _ (hT x hx)

theorem opLat_dp {M N : AddSubgroup V} (hM : G.DPStable M) (hNZ : ZpClosed (p := p) N) (hN : G.DPStable N) :
    (G.restr hW).endRep.DPStable (opLat (W := W) M N) := by
  intro a b hab k T hT x hx
  rw [endRep_dpow, LinearMap.sum_apply, Submodule.coe_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, Module.End.mul_apply, Module.End.mul_apply]
  refine zpClosed_smul hNZ (z := (-1) ^ (k - i)) (by simp) ?_
  rw [G.coe_dpow_restr hW]
  refine hN a b hab i _ (hT _ ?_)
  rw [G.coe_dpow_restr hW]
  exact hM a b hab _ _ hx

theorem opLat_comp {M N : AddSubgroup V} (hM : G.CompStable M) (hN : G.CompStable N) :
    (G.restr hW).endRep.CompStable (opLat (W := W) M N) := by
  intro μ T hT x hx
  rw [endRep_comp, LinearMap.sum_apply, Submodule.coe_sum]
  exact AddSubgroup.sum_mem _ fun ν _ => hN _ _ (hT _ (hM ν _ hx))

/-- **The string bound at weight `0` in `End W`**: a nonzero `(ad e)^(k) T` with `T` of weight `0` has `k ≤ l`. -/
theorem endRep_string {l : ℕ} (hl : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ l) {T : Module.End ℚ_[p] W}
    (hT : (G.restr hW).endRep.IsWt 0 T) {a b : Fin n} (hab : a ≠ b) (k : ℕ)
    (hk : dpow ((G.restr hW).endRep.E a b) k T ≠ 0) : (0 : ℤ) - 0 + k ≤ l := by
  have hw := hT.dpow a b k
  rw [GlRep.IsWt, endRep_comp] at hw
  rw [← hw] at hk
  obtain ⟨ν, hν, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  have hwts : ∀ ξ ∈ (G.restr hW).wtsU, ξ ∈ G.wts W := by
    intro ξ hξ
    obtain ⟨y, -, hy⟩ := (Set.Finite.mem_toFinset _).mp hξ
    exact ⟨y, y.2, fun h => hy (Subtype.ext (by rw [restr_comp, h]; rfl))⟩
  have h2 : 0 + (k : ℤ) • rt a b + ν ∈ (G.restr hW).wtsU := by
    by_contra h
    rw [add_comm ν, comp_eq_zero_of_notMem _ h, zero_mul, zero_mul] at hne
    exact hne rfl
  have e1 := hl _ (hwts _ h2) a b
  have e2 := hl _ (hwts _ hν) b a
  simp only [Pi.add_apply, Pi.smul_apply, rt_apply_left hab, rt_apply_right hab, smul_eq_mul,
    Pi.zero_apply] at e1
  linarith

end OpLat

/-! ## Isotypic and Kostant integrality -/

section IsoInt

variable {W : Submodule ℚ_[p] V} [FiniteDimensional ℚ_[p] W] (hW : G.Stable W)

open Classical in
/-- **On an isotypic part**, the type projectors act by `0` or `1`. -/
theorem typeProj_of_mem_isoPart (T : Set (Fin n → ℤ)) {la : Fin n → ℤ} {x : V} (hx : x ∈ G.isoPart W la) :
    G.typeProj hW T x = if la ∈ T then x else 0 := by
  split_ifs with h
  · exact G.typeProj_of_mem hW T (Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem h hx))
  · exact G.typeProj_of_mem_compl hW T (Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem h hx))

omit [FiniteDimensional ℚ_[p] W] in
theorem mem_wts_of_isoPart_ne {la : Fin n → ℤ} {x : V} (hx : x ∈ G.isoPart W la) (hx0 : x ≠ 0) :
    la ∈ G.wts W := by
  by_contra hla
  have hbot : G.isoPart W la = ⊥ := by
    refine le_bot_iff.mp (iSup_le fun i => ?_)
    obtain ⟨h, hhW, hh⟩ := i
    have : h = 0 := by by_contra h0; exact hla (G.mem_wts_of_isWt hhW hh.1 h0)
    change G.gen {h} ≤ ⊥
    rw [this, gen_zero]
  rw [hbot] at hx
  exact hx0 ((Submodule.mem_bot ℚ_[p]).mp hx)

open Classical in
/-- **Type projectors are finite sums of isotypic projectors** on `W`. -/
theorem typeProj_eq_sum (T : Set (Fin n → ℤ)) {x : V} (hx : x ∈ W) :
    G.typeProj hW T x = ∑ la ∈ (G.wts_finite W).toFinset with la ∈ T, G.typeProj hW {la} x := by
  classical
  rw [← G.iSup_isoPart hW] at hx
  refine Submodule.iSup_induction (motive := fun x => G.typeProj hW T x =
    ∑ la ∈ (G.wts_finite W).toFinset with la ∈ T, G.typeProj hW {la} x) _ hx ?_ (by simp)
    (fun x y hx hy => by rw [map_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add])
  intro la₀ x hx
  by_cases hx0 : x = 0
  · subst hx0; simp
  rw [G.typeProj_of_mem_isoPart hW T hx]
  simp only [G.typeProj_of_mem_isoPart hW _ hx, Set.mem_singleton_iff]
  rw [Finset.sum_ite_eq]
  have hmem := G.mem_wts_of_isoPart_ne hx hx0
  by_cases hT : la₀ ∈ T <;> simp [hT, hmem]

/-- **Isotypic and Kostant integrality** (T6(c),(d), abstract): for `M` a `ℤ_p`-closed, divided-power stable,
weight-stable subgroup and `W` of spread `≤ l`, `p^(2·projExp p n l)` times the `λ`-isotypic component of an
`x ∈ M ∩ W` lies in the Kostant span of the integral highest weight vectors of weight `λ` in `W`. -/
theorem isoKostant_int {M : AddSubgroup V} (hZ : ZpClosed (p := p) M) (hM : G.DPStable M) (hC : G.CompStable M)
    {l : ℕ} (hl : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ l) (la : Fin n → ℤ) {x : V} (hxM : x ∈ M) (hxW : x ∈ W) :
    (p : ℚ_[p]) ^ (2 * projExp p n l) • G.typeProj hW {la} x ∈
      G.kostantSpan {v | G.IsHw la v ∧ v ∈ W ∧ v ∈ M} := by
  set S := {v | G.IsHw la v ∧ v ∈ W ∧ v ∈ M}
  set N := G.kostantSpan S
  by_cases hla : Antitone la
  · obtain ⟨d, hd⟩ := G.isoAvg_spec hW la
    obtain ⟨hD0, hD⟩ := Classical.choose_spec (G.dpow_nil hW)
    set e := projExp p n l
    -- the scaled highest weight projector maps `M ∩ W` into `N`
    have hS' : (p : ℚ_[p]) ^ e • G.hwOp hW la ∈ opLat (W := W) M N := by
      intro y hy
      rw [LinearMap.smul_apply, Submodule.coe_smul, hwOp_apply]
      have hP := G.isHw_xproj hW hD hla (G.isWt_comp la (y : V)) (G.comp_mem hW la y.2)
      refine G.subset_kostantSpan S ⟨⟨hP.1.smul _, fun a b hab => by rw [map_smul, hP.2 a b hab, smul_zero]⟩,
        ?_, ?_⟩
      · exact W.smul_mem _ (G.xproj_mem hW _ _ _ (G.comp_mem hW la y.2))
      · exact G.hwProj_int hW hZ hM hl hla _ (G.comp_mem hW la y.2) (G.isWt_comp la _) (hC la _ hy)
    have hNC : G.CompStable N := G.kostantSpan_comp fun s hs => ⟨la, hs.1.1⟩
    have hC0 := G.opLat_comp hW hC hNC 0 _ hS'
    have hX := (G.restr hW).endRep.xproj_int (W := ⊤) (fun _ _ _ _ => Submodule.mem_top)
      (opLat_zp M (G.kostantSpan_zp S)) (G.opLat_dp hW hM (G.kostantSpan_zp S) (G.kostantSpan_dp S)) 0
      (Classical.choose ((G.restr hW).endRep.dpow_nil (W := ⊤) fun _ _ _ _ => Submodule.mem_top))
      (fun z _ hz a b hab k hk => by simpa using G.endRep_string hW hl hz (ne_of_lt hab) k hk)
      (List.finRange n) (List.pairwise_lt_finRange n) (fun _ _ _ _ _ => le_rfl) (by simp) _ Submodule.mem_top
      ((G.restr hW).endRep.isWt_comp 0 _) hC0
    rw [map_smul, map_smul] at hX
    have hx := hX ⟨x, hxW⟩ hxM
    simp only [LinearMap.smul_apply, Submodule.coe_smul, List.length_finRange] at hx
    rw [hd x hxW, two_mul, pow_add, mul_smul, smul_comm ((p : ℚ_[p]) ^ e) ((d : ℕ) : ℚ_[p]),
      smul_comm ((p : ℚ_[p]) ^ e) ((d : ℕ) : ℚ_[p])]
    exact zpClosed_smul (G.kostantSpan_zp S) (z := (d : ℤ_[p])) (by simp) hx
  · have hbot : G.isoPart W la = ⊥ := by
      refine le_bot_iff.mp (iSup_le fun i => ?_)
      obtain ⟨h, hhW, hh⟩ := i
      have : h = 0 := by by_contra h0; exact hla (G.antitone_of_hw hW hh hhW h0)
      change G.gen {h} ≤ ⊥
      rw [this, gen_zero]
    have := G.typeProj_mem hW {la} x
    rw [G.isoSum_singleton, hbot, Submodule.mem_bot] at this
    rw [this, smul_zero]; exact zero_mem _

/-- **Isotypic integrality** (T6(c), abstract): `p^(2·projExp p n l)·Q_λ(M ∩ W) ⊆ M`. -/
theorem isoProj_int {M : AddSubgroup V} (hZ : ZpClosed (p := p) M) (hM : G.DPStable M) (hC : G.CompStable M)
    {l : ℕ} (hl : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ l) (la : Fin n → ℤ) {x : V} (hxM : x ∈ M) (hxW : x ∈ W) :
    (p : ℚ_[p]) ^ (2 * projExp p n l) • G.typeProj hW {la} x ∈ M :=
  G.kostantSpan_le (fun _ hv => hv.2.2) hZ hM (G.isoKostant_int hW hZ hM hC hl la hxM hxW)

include hW in
/-- **Kostant integrality** (T6(b),(d), abstract): an integral `λ`-isotypic vector, times `p^(2·projExp p n l)`, lies
in the Kostant span of the integral highest weight vectors of weight `λ` in `W`. -/
theorem kostant_int {M : AddSubgroup V} (hZ : ZpClosed (p := p) M) (hM : G.DPStable M) (hC : G.CompStable M)
    {l : ℕ} (hl : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ l) (la : Fin n → ℤ) {x : V} (hx : x ∈ G.isoPart W la)
    (hxM : x ∈ M) :
    (p : ℚ_[p]) ^ (2 * projExp p n l) • x ∈ G.kostantSpan {v | G.IsHw la v ∧ v ∈ W ∧ v ∈ M} := by
  have h := G.isoKostant_int hW hZ hM hC hl la hxM (G.isoPart_le hW la hx)
  rwa [G.typeProj_of_mem hW {la} (by rwa [G.isoSum_singleton])] at h

/-- **Type projector integrality**: `p^(2·projExp p n l)·P_T(M ∩ W) ⊆ M` for every type set `T`. -/
theorem typeProj_int {M : AddSubgroup V} (hZ : ZpClosed (p := p) M) (hM : G.DPStable M) (hC : G.CompStable M)
    {l : ℕ} (hl : ∀ μ ∈ G.wts W, ∀ a b, μ a - μ b ≤ l) (T : Set (Fin n → ℤ)) {x : V} (hxM : x ∈ M)
    (hxW : x ∈ W) : (p : ℚ_[p]) ^ (2 * projExp p n l) • G.typeProj hW T x ∈ M := by
  classical
  rw [G.typeProj_eq_sum hW T hxW, Finset.smul_sum]
  exact AddSubgroup.sum_mem _ fun la _ => G.isoProj_int hW hZ hM hC hl la hxM hxW

end IsoInt

end GlRep
