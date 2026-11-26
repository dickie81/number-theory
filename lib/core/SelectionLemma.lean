import Mathlib

/-!
# The selection lemma

Part L4b of the gain's local theory: pure algebra over a discrete valuation ring `O` with uniformiser `ϖ`. Let `M` be
a free `O`-module with basis `(b_i)_{i ∈ I}`, `d = |I|`, and `z_v`, `v ∈ srv`, commuting endomorphisms of `M`, with
exponents `E_v` and excesses `S_v`. The *selected span* (`selSpan`) is
`N = Σ_{B ⊆ srv} ϖ^{S(srv ∖ B)}·z_B(M)`, where `z_B = ∏_{v ∈ B} z_v` and `S(C) = Σ_{v ∈ C} S_v`; it is spanned by the
vectors `∏_{v ∈ B} z_v(ϖ^{S(srv ∖ B)}x)`. With `τ = Σ_{v ∈ srv} E_v`, the lemma bounds the colength of `N ∩ ϖ^τM`
in `M`: the certificate takes this lattice, inside `ϖ^τM`, at each served prime (`z_v = y_v^m`, `y_v` the Hecke
operator at the orbit `v`).

**The hypothesis.** Each basis vector `b_i` carries a *failure set* `A_i`: the operators it is not good for. The
operator `z_v` is *relatively near-invertible* up to `ϖ^{E_v}` (`NearInv`) if, whenever `v ∉ A_i`,
`ϖ^{E_v}·b_i = z_v(w)` with `w` a combination of basis vectors `b_j` with `A_j ⊆ A_i ∪ {v}`. So `z_v` reaches
`ϖ^{E_v}` times its good part `U_v = span{b_i : v ∉ A_i}` (a saturated submodule of corank `#{i : v ∈ A_i}`), and the
preimage can be chosen without spoiling the goodness of the vector for the other operators. The model is a tensor
product `M = ⊗_v M_v` with `z_v` acting on the factor `M_v`, and on each factor a basis made of a basis of a saturated
part reached by `z_v` up to `ϖ^{E_v}` and a basis of a complement; the failure set of a tensor product of basis vectors
is the set of factors where it lies in the complement. There `NearInv` holds as soon as each `z_v` reaches its part
on its own factor: a preimage of `ϖ^{E_v}·b_i` is `w_v ⊗ (the other factors of b_i)`, whose basis vectors differ from
`b_i` only in the factor `v`. This is what L4a is to produce from the local lattice problems: at a vertex the Hecke
operators at different orbits act on different tensor factors.

**Main results.**
* `length_le`: `length(M/(N ∩ ϖ^τM)) ≤ d·τ + Σ_{v ∈ srv} S_v·#{i : v ∈ A_i}`.
* `selection`, the form of the planning spec: for `z_v = y_v^m`, `E_v = m·e_v` and failure counts
  `#{i : v ∈ A_i} ≤ m·κ_v·d` (that is, `U_v` has rank at least `(1 − m·κ_v)·d`), the colength is at most
  `d·(τ + S_max·m·Σ_v κ_v)`. The spec asked for `d·(τ + 2·S_max·m·Σ_v κ_v)` under `m·Σ_v κ_v ≤ 1/2`; the constant
  here is `1`, and the smallness condition is not needed.

**The route.** For `B ⊆ srv` disjoint from `C`, `ϖ^{E(B)}` times the span of the `b_j` with `A_j ⊆ C` lies in
`z_B` of the span of the `b_j` with `A_j ⊆ C ∪ B` (`smul_mem_map_prodOp`): by induction on `B`, one `NearInv` step
for the new index `v` (`smul_mem_map_of_nearInv`), then the induction hypothesis for `C ∪ {v}`; commutativity lets
`z_v` act first (`prodOp_insert`). For `b_i`, take `C = A_i` and `B = srv ∖ A_i`, so that `srv ∖ B = srv ∩ A_i`:
`ϖ^{τ + S(srv ∩ A_i)}·b_i = ϖ^{S(srv ∖ B)}·ϖ^{E(srv ∩ A_i)}·ϖ^{E(B)}·b_i` lies in `ϖ^{S(srv ∖ B)}·z_B(M) ⊆ N`, and in
`ϖ^τM`. So `N ∩ ϖ^τM` contains the diagonal lattice spanned by the `ϖ^{τ + S(srv ∩ A_i)}·b_i`, and `M` modulo it is a
quotient of `Π_i O/ϖ^{n_i}`, of length `Σ_i n_i` (`length_quotient_le`). Finally
`Σ_i S(srv ∩ A_i) = Σ_{v ∈ srv} S_v·#{i : v ∈ A_i}`. No inclusion–exclusion over `B` is needed.

**Why not the per-operator hypothesis.** The spec proposed, for each `v` separately, a saturated `U_v ⊆ M` of rank at
least `(1 − m·κ_v)·d` with `ϖ^{m·e_v}·U_v ⊆ y_v^m(M)`. With that hypothesis the bound is false. Take `d = 8`,
`srv` of four indices, every `y_v` equal to the shift `A` with `A e_1 = 0`, `A e_k = e_{k−1}` for `2 ≤ k ≤ 5` and
`A e_k = e_k` for `k ≥ 6`, and `m = 1`, `e_v = 0`, `S_v = 1`, `κ_v = 1/8`. Then `U = A(M)` is saturated, `A`-stable,
of rank `7`, and `m·Σ_v κ_v = 1/2`; but `N = Σ_β ϖ^{4−β}A^β(M)` (`β = |B|`) is spanned by the `ϖ^{k−1}e_k`
(`k ≤ 5`) and the `e_k` (`k ≥ 6`), of colength `0 + 1 + 2 + 3 + 4 = 10 > 8 = d·(τ + 2·S_max·m·Σ_v κ_v)`. With `n`
copies of a longer shift the colength is `S·n(n + 1)/2` against `2·S·n`: the per-operator hypothesis lets the
failures of the different operators pile up on the same vectors (the kernel of `A^β` grows with `β`). Asking `U_v` to
be stable under the operators does not help (it holds above), and `e_v ≥ 1` does not either (take `y_v = ϖ^{e}A` and
`S > e`). The sketch's elementary symmetric functions amount to bounding the joint failures of a set `C` of operators
by `d·Π_{v ∈ C} m·κ_v`: an independence that the tensor structure provides and a per-operator statement cannot.
`NearInv` records it on a common basis.
-/

namespace SelectionLemma

open Submodule Finset

noncomputable section

variable {O : Type*} [CommRing O] {ϖ : O}
variable {M : Type*} [AddCommGroup M] [Module O M]
variable {ι I : Type*} [DecidableEq ι]

/-- The **product of the operators** `z_v`, `v ∈ B`, in the order of `B.toList` (in any order, when they commute:
`prodOp_insert`). -/
def prodOp (z : ι → Module.End O M) (B : Finset ι) : Module.End O M :=
  (B.toList.map z).prod

/-- The **selected span** `N = Σ_{B ⊆ srv} ϖ^{S(srv ∖ B)}·z_B(M)`, spanned by the vectors
`ϖ^{Σ_{v ∈ srv ∖ B} S_v}·∏_{v ∈ B} z_v(x)`. -/
def selSpan (ϖ : O) (srv : Finset ι) (z : ι → Module.End O M) (S : ι → ℕ) : Submodule O M :=
  span O (⋃ B ∈ srv.powerset, Set.range fun x => ϖ ^ (∑ v ∈ srv \ B, S v) • prodOp z B x)

/-- **Relative near-invertibility** of `y` at `v` up to `ϖ^e`, for a basis `b` with failure sets `A`: every basis
vector `b_i` whose failure set avoids `v` has `ϖ^e·b_i = y(w)` with `w` in the span of the basis vectors whose
failure sets lie in `A_i ∪ {v}`. -/
def NearInv (ϖ : O) (b : Module.Basis I O M) (A : I → Finset ι) (v : ι) (y : Module.End O M) (e : ℕ) : Prop :=
  ∀ i, v ∉ A i → ϖ ^ e • b i ∈ (span O (b '' {j | A j ⊆ insert v (A i)})).map y

/-- **Commuting operators**: the product over `insert v B` is `z_v` times the product over `B`. -/
theorem prodOp_insert {z : ι → Module.End O M} {srv B : Finset ι} {v : ι}
    (hcomm : ∀ u ∈ srv, ∀ w ∈ srv, Commute (z u) (z w)) (hB : insert v B ⊆ srv) (hv : v ∉ B) :
    prodOp z (insert v B) = z v * prodOp z B := by
  unfold prodOp
  rw [List.Perm.prod_eq' ((Finset.toList_insert hv).map z), List.map_cons, List.prod_cons]
  refine List.pairwise_of_forall_mem_list fun a ha c hc => ?_
  simp only [List.mem_map, Finset.mem_toList] at ha hc
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hc
  exact hcomm u (hB hu) w (hB hw)

/-- **One step, on a span**: under `NearInv` at `v`, `ϖ^e` times a vector in the span of the basis vectors with
failure sets in `C ∌ v` is the image under `y` of a vector in the span of those with failure sets in `C ∪ {v}`. -/
theorem smul_mem_map_of_nearInv {b : Module.Basis I O M} {A : I → Finset ι} {v : ι} {y : Module.End O M} {e : ℕ}
    (h : NearInv ϖ b A v y e) {C : Finset ι} (hv : v ∉ C) {x : M} (hx : x ∈ span O (b '' {j | A j ⊆ C})) :
    ϖ ^ e • x ∈ (span O (b '' {j | A j ⊆ insert v C})).map y := by
  have hle : span O (b '' {j | A j ⊆ C}) ≤
      ((span O (b '' {j | A j ⊆ insert v C})).map y).comap (ϖ ^ e • LinearMap.id) := by
    rw [span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    refine map_mono (span_mono (Set.image_mono fun k hk => ?_)) (h j fun hvj => hv (hj hvj))
    exact (hk : A k ⊆ _).trans (Finset.insert_subset_insert v hj)
  simpa using hle hx

/-- **The products reach the parts that avoid their indices**: for `B ⊆ srv` disjoint from `C`,
`ϖ^{Σ_{v ∈ B} E_v}` times a vector in the span of the basis vectors with failure sets in `C` is `z_B` of a vector in
the span of those with failure sets in `C ∪ B`. -/
theorem smul_mem_map_prodOp {b : Module.Basis I O M} {A : I → Finset ι} {srv : Finset ι}
    {z : ι → Module.End O M} (hcomm : ∀ u ∈ srv, ∀ w ∈ srv, Commute (z u) (z w)) {E : ι → ℕ}
    (hNI : ∀ v ∈ srv, NearInv ϖ b A v (z v) (E v)) (B : Finset ι) (hB : B ⊆ srv) (C : Finset ι)
    (hBC : Disjoint B C) {x : M} (hx : x ∈ span O (b '' {j | A j ⊆ C})) :
    ϖ ^ (∑ v ∈ B, E v) • x ∈ (span O (b '' {j | A j ⊆ C ∪ B})).map (prodOp z B) := by
  induction B using Finset.induction_on generalizing C x with
  | empty => simpa [prodOp] using hx
  | insert v B hvB ih =>
    have hv : v ∈ srv := hB (mem_insert_self _ _)
    have hvC : v ∉ C := Finset.disjoint_left.mp hBC (mem_insert_self _ _)
    obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp (smul_mem_map_of_nearInv (hNI v hv) hvC hx)
    have hdis : Disjoint B (insert v C) :=
      Finset.disjoint_insert_right.mpr ⟨hvB, (Finset.disjoint_insert_left.mp hBC).2⟩
    obtain ⟨w', hw', hw'w⟩ := Submodule.mem_map.mp (ih ((subset_insert _ _).trans hB) (insert v C) hdis hw)
    refine Submodule.mem_map.mpr ⟨w', ?_, ?_⟩
    · have hCB : insert v C ∪ B = C ∪ insert v B := by
        ext u; simp only [mem_union, mem_insert]; tauto
      rwa [hCB] at hw'
    · rw [prodOp_insert hcomm hB hvB, Module.End.mul_apply, hw'w, map_smul, hwx, sum_insert hvB, pow_add,
        smul_smul, mul_comm]

variable [IsDomain O] [IsDiscreteValuationRing O] [Fintype I]

/-- **Colength of a lattice containing a diagonal one**: if `T` contains `ϖ^{n_i}·b_i` for every basis vector, then
`M/T` has length at most `Σ_i n_i`, as it is a quotient of `Π_i O/ϖ^{n_i}`. -/
theorem length_quotient_le (hϖ : Irreducible ϖ) (b : Module.Basis I O M) (T : Submodule O M) (n : I → ℕ)
    (hT : ∀ i, ϖ ^ n i • b i ∈ T) : Module.length O (M ⧸ T) ≤ ∑ i, (n i : ℕ∞) := by
  let f : ∀ i, (O ⧸ Ideal.span {ϖ ^ n i}) →ₗ[O] M ⧸ T := fun i =>
    (Ideal.span {ϖ ^ n i}).liftQ (T.mkQ ∘ₗ LinearMap.toSpanSingleton O M (b i)) (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simpa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] using hT i)
  let ψ : (∀ i, O ⧸ Ideal.span {ϖ ^ n i}) →ₗ[O] M ⧸ T := ∑ i, f i ∘ₗ LinearMap.proj i
  have hψ : Function.Surjective ψ := by
    rintro ⟨x⟩
    refine ⟨fun i => Submodule.Quotient.mk (b.repr x i), ?_⟩
    have : ψ (fun i => Submodule.Quotient.mk (b.repr x i)) = T.mkQ (∑ i, b.repr x i • b i) := by
      rw [LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    rw [this, b.sum_repr]
    rfl
  calc Module.length O (M ⧸ T) ≤ Module.length O (∀ i, O ⧸ Ideal.span {ϖ ^ n i}) :=
        Module.length_le_of_surjective ψ hψ
    _ = ∑ i, (n i : ℕ∞) := by
        rw [Module.length_pi_of_fintype]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
          IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- **The selection lemma, sharp form**: for commuting `z_v`, relatively near-invertible up to `ϖ^{E_v}` on a basis
with failure sets `A_i`, the selected span meets `ϖ^τM`, `τ = Σ_{v ∈ srv} E_v`, in a lattice of colength at most
`d·τ + Σ_{v ∈ srv} S_v·#{i : v ∈ A_i}`. -/
theorem length_le (hϖ : Irreducible ϖ) (b : Module.Basis I O M) (srv : Finset ι) (z : ι → Module.End O M)
    (hcomm : ∀ u ∈ srv, ∀ v ∈ srv, Commute (z u) (z v)) (E S : ι → ℕ) (A : I → Finset ι)
    (hNI : ∀ v ∈ srv, NearInv ϖ b A v (z v) (E v)) :
    Module.length O (M ⧸ selSpan ϖ srv z S ⊓ Ideal.span {ϖ ^ ∑ v ∈ srv, E v} • ⊤) ≤
      ((Fintype.card I * ∑ v ∈ srv, E v + ∑ v ∈ srv, S v * #{i | v ∈ A i} : ℕ) : ℕ∞) := by
  set τ := ∑ v ∈ srv, E v with hτ
  have key : ∀ i, ϖ ^ (τ + ∑ v ∈ srv ∩ A i, S v) • b i ∈ selSpan ϖ srv z S ⊓ Ideal.span {ϖ ^ τ} • ⊤ := by
    intro i
    refine ⟨?_, ?_⟩
    · have hB : srv \ A i ⊆ srv := sdiff_subset
      obtain ⟨w, -, hw⟩ := Submodule.mem_map.mp (smul_mem_map_prodOp hcomm hNI (srv \ A i) hB (A i)
        sdiff_disjoint (subset_span ⟨i, Finset.Subset.refl (A i), rfl⟩))
      have h1 : srv \ (srv \ A i) = srv ∩ A i := by
        ext u; simp only [mem_sdiff, mem_inter]; tauto
      have h2 : τ = ∑ v ∈ srv ∩ A i, E v + ∑ v ∈ srv \ A i, E v := by
        rw [hτ, ← sum_union (disjoint_sdiff_inter srv (A i)).symm, union_comm, sdiff_union_inter]
      apply subset_span
      refine Set.mem_iUnion₂.mpr ⟨srv \ A i, mem_powerset.mpr hB, ϖ ^ (∑ v ∈ srv ∩ A i, E v) • w, ?_⟩
      simp only
      rw [map_smul, hw, h1, h2, smul_smul, smul_smul, ← pow_add, ← pow_add]
      ring_nf
    · rw [pow_add, mul_smul]
      exact smul_mem_smul (Ideal.mem_span_singleton_self _) mem_top
  refine (length_quotient_le hϖ b _ _ key).trans (le_of_eq ?_)
  norm_cast
  rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul]
  congr 1
  simp_rw [← filter_mem_eq_inter, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]

/-- **The selection lemma** (L4b), in the form of the planning spec: for commuting `y_v`, with `y_v^m` relatively
near-invertible up to `ϖ^{m·e_v}` on a basis whose failure sets satisfy `#{i : v ∈ A_i} ≤ m·κ_v·d` (the good part of
`y_v^m` has rank at least `(1 − m·κ_v)·d`), and `S_v ≤ S_max`, the selected span `N` of the `y_v^m` meets
`ϖ^τM`, `τ = Σ_v m·e_v`, in a lattice of colength `ℓ ≤ d·(τ + S_max·m·Σ_v κ_v)`. -/
theorem selection (hϖ : Irreducible ϖ) (b : Module.Basis I O M) (srv : Finset ι) (y : ι → Module.End O M)
    (hcomm : ∀ u ∈ srv, ∀ v ∈ srv, Commute (y u) (y v)) (m : ℕ) (e S : ι → ℕ) (Smax : ℕ)
    (hS : ∀ v ∈ srv, S v ≤ Smax) (κ : ι → ℝ) (A : I → Finset ι)
    (hNI : ∀ v ∈ srv, NearInv ϖ b A v (y v ^ m) (m * e v))
    (hdef : ∀ v ∈ srv, (#{i | v ∈ A i} : ℝ) ≤ m * κ v * Module.finrank O M) :
    ∃ ℓ : ℕ, Module.length O (M ⧸ selSpan ϖ srv (fun v => y v ^ m) S ⊓
        Ideal.span {ϖ ^ ∑ v ∈ srv, m * e v} • ⊤) = ℓ ∧
      (ℓ : ℝ) ≤ Module.finrank O M * ((∑ v ∈ srv, m * e v : ℕ) + Smax * (m * ∑ v ∈ srv, κ v)) := by
  have h := length_le hϖ b srv (fun v => y v ^ m) (fun u hu v hv => (hcomm u hu v hv).pow_pow m m)
    (fun v => m * e v) S A hNI
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h)
  refine ⟨ℓ, hℓ.symm, ?_⟩
  rw [← hℓ, Nat.cast_le] at h
  rw [Module.finrank_eq_card_basis b] at hdef ⊢
  have hS' : ∀ v ∈ srv, (S v : ℝ) * #{i | v ∈ A i} ≤ Smax * (m * κ v * Fintype.card I) := fun v hv =>
    mul_le_mul (by exact_mod_cast hS v hv) (hdef v hv) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc (ℓ : ℝ) ≤ Fintype.card I * (∑ v ∈ srv, m * e v : ℕ) + ∑ v ∈ srv, (S v : ℝ) * #{i | v ∈ A i} := by
        exact_mod_cast h
    _ ≤ Fintype.card I * (∑ v ∈ srv, m * e v : ℕ) + ∑ v ∈ srv, Smax * (m * κ v * Fintype.card I) := by
        exact (add_le_add_iff_left _).mpr (sum_le_sum hS')
    _ = Fintype.card I * ((∑ v ∈ srv, m * e v : ℕ) + Smax * (m * ∑ v ∈ srv, κ v)) := by
        rw [mul_add]
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact sum_congr rfl fun v _ => by ring

end

end SelectionLemma
