import Mathlib
import PlaceLattice

/-!
# Hermitian lattices over a totally complex field

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 4). Hermitian lattices over the
ring of integers `O_K` of a totally complex number field `K` are lattices with places (`placeLattice`), and maps between
them that commute with `O_K` form frames whose heights are averaged over the places (`frame`). Alpöge's frames are of
this kind.

**The model.** `E` is a complex inner product space, the orthogonal sum of subspaces `V v` at the complex places `v` of
`K`. An element `k ∈ K` acts by `σ_v(k)` on `V v` (`act V (emb k)`), where `σ_v` is the embedding that `v` chooses. A
hermitian `O_K`-lattice is a discrete subgroup `Λ` that `O_K` keeps (`Stable`). Every hermitian `O_K`-module `M` of
finite rank is one, in `E = ⊕_v M ⊗_{σ_v} ℂ` with its metrics. The real structure on `E` is `Re⟨·,·⟩`; other
normalisations of the metric shift all slopes by one constant.

**The class** (`stableSat`) is the set of `O_K`-stable saturated sublattices of `Λ`, a sublattice of `Sat Λ`. Their
spans are balanced (`balanced`), in two steps.
* **Compatible.** The real span `U` of a stable `a` is stable under all of `K ⊗ ℝ = ∏_v ℂ`, as the images of `O_K` span
  it over `ℝ` (`span_emb`, from Mathlib's `latticeBasis`; `act_mem`). So `U` contains its parts at the places, and is
  their sum (`iSup_inf_eq`).
* **Equal dimensions** (`finrank_inf_le`). At two places `v₀` and `v`, pick `x_i ∈ a`, `d` of them, whose parts at `v₀`
  form a complex basis of the part of `U` there. The map `(c_i) ↦ Σ c_i x_i` on `O_K^d` is injective, since its part
  at `v₀` is `Σ σ_{v₀}(c_i) x_{i,v₀}`. So its image has rank `d·[K:ℚ] = 2d·n_∞`. At each place, the part of the image
  lies in the complex span of the `x_{i,w}`, of real dimension at most `2d`, and the parts add up to at least the
  whole. So at `v` the image, hence `U`, has dimension at least `2d`, the dimension of `U` at `v₀`.

No `K`-vector space structure, Galois group or unit is needed.

**Frames** (`frame`). Maps that commute with `O_K` keep the classes (`Stable.img`, `Stable.preimg`). So hermitian
lattices and such maps form a `SlopeFrame.Frame`, with heights `h̄ = n_∞⁻¹ Σ_v log‖φ‖_v`. The archive's slopes
`μ = 2·deg/rk_ℤ − log 2 + log|d_K|/[K:ℚ]` and heights `h(φ) = n_∞⁻¹ Σ_v log‖φ_v‖² = 2h̄` are twice these, the slopes
shifted by a constant (`PlaceLattice`).
-/

namespace HermitianLattice

open Module Submodule NumberField NumberField.InfinitePlace EuclidLattice PlaceLattice GramVolume

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical

variable {K : Type} [Field K] [NumberField K]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The complex places of `K`. -/
abbrev Pl (K : Type) [Field K] := {w : InfinitePlace K // w.IsComplex}

/-- `K` at its complex places: `k ↦ (σ_v k)_v`, with `σ_v` the embedding that the place `v` chooses. -/
noncomputable def emb : K →+* (Pl K → ℂ) :=
  RingHom.pi fun v => v.1.embedding

/-- `z : Pl K → ℂ` acts on `E` by `z v` on `V v`; `k ∈ K` acts by `emb k`. -/
noncomputable def act (V : Pl K → Submodule ℂ E) (z : Pl K → ℂ) : E →ₗ[ℂ] E :=
  ∑ v, z v • ((V v).starProjection : E →ₗ[ℂ] E)

/-- A subgroup `a` is stable under `O_K` when each `k ∈ O_K` sends it into itself. -/
def Stable (V : Pl K → Submodule ℂ E) (a : Submodule ℤ E) : Prop :=
  ∀ k : 𝓞 K, ∀ x ∈ a, act V (emb (k : K)) x ∈ a

variable {V : Pl K → Submodule ℂ E}

/-- `act V z x = Σ_v z v·π_v x`. -/
theorem act_apply (z : Pl K → ℂ) (x : E) : act V z x = ∑ v, z v • (V v).starProjection x := by
  simp [act]

/-- `act V` is additive in `z`. -/
theorem act_add_left (z z' : Pl K → ℂ) (x : E) : act V (z + z') x = act V z x + act V z' x := by
  simp [act_apply, add_smul, Finset.sum_add_distrib]

/-- `act V` is `ℝ`-linear in `z`. -/
theorem act_smul_left (r : ℝ) (z : Pl K → ℂ) (x : E) : act V (r • z) x = r • act V z x := by
  rw [act_apply, act_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [Pi.smul_apply, smul_assoc]

/-- The part of `act V z x` at `v` is `z v` times the part of `x`. -/
theorem starProjection_act (hV : Pairwise fun v w => V v ⟂ V w) (z : Pl K → ℂ) (x : E) (v : Pl K) :
    (V v).starProjection (act V z x) = z v • (V v).starProjection x := by
  rw [act_apply, map_sum, Finset.sum_eq_single v]
  · rw [map_smul, starProjection_eq_self_iff.2 (starProjection_apply_mem (V v) x)]
  · intro w _ hwv
    rw [map_smul, (starProjection_apply_eq_zero_iff (V v)).2 ((hV hwv) (starProjection_apply_mem (V w) x)),
      smul_zero]
  · simp

omit [FiniteDimensional ℂ E] in
/-- **`O_K` spans `K ⊗ ℝ`**: the vectors `(σ_v k)_v`, `k ∈ O_K`, span `∏_v ℂ` over `ℝ`. Mathlib's `latticeBasis`, the
image of an integral basis, is a basis of the mixed space. -/
theorem span_emb : span ℝ (Set.range fun k : 𝓞 K => emb (k : K)) = ⊤ := by
  have h := congrArg (map (LinearMap.snd ℝ ({w : InfinitePlace K // IsReal w} → ℝ) (Pl K → ℂ)))
    (mixedEmbedding.latticeBasis K).span_eq
  rw [map_span, Submodule.map_top, Submodule.range_snd] at h
  rw [eq_top_iff, ← h]
  refine span_mono ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨RingOfIntegers.basis K i, funext fun v => by
    simp [emb, mixedEmbedding.latticeBasis_apply, integralBasis_apply]⟩

/-- A real subspace stable under `O_K` is stable under all of `K ⊗ ℝ = ∏_v ℂ`. -/
theorem act_mem {U : Submodule ℝ E} (hU : ∀ k : 𝓞 K, ∀ x ∈ U, act V (emb (k : K)) x ∈ U) (z : Pl K → ℂ)
    {x : E} (hx : x ∈ U) : act V z x ∈ U := by
  have hz : z ∈ span ℝ (Set.range fun k : 𝓞 K => emb (k : K)) := by
    rw [span_emb]
    exact mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    exact hU k x hx
  | zero => simp [act_apply]
  | add z z' _ _ h h' =>
    rw [act_add_left]
    exact U.add_mem h h'
  | smul r z _ h =>
    rw [act_smul_left]
    exact U.smul_mem r h

/-- A real subspace stable under `O_K` contains the parts of its vectors at each place. -/
theorem starProjection_mem {U : Submodule ℝ E} (hU : ∀ k : 𝓞 K, ∀ x ∈ U, act V (emb (k : K)) x ∈ U) (v : Pl K)
    {x : E} (hx : x ∈ U) : (V v).starProjection x ∈ U := by
  have := act_mem hU (Pi.single v 1) hx
  rwa [act_apply, Finset.sum_eq_single v (fun w _ hw => by simp [hw]) (by simp), Pi.single_eq_same,
    one_smul] at this

/-- The real span of a stable subgroup is stable. -/
theorem span_stable {a : Submodule ℤ E} (ha : Stable V a) (k : 𝓞 K) {x : E} (hx : x ∈ span ℝ (a : Set E)) :
    act V (emb (k : K)) x ∈ span ℝ (a : Set E) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact subset_span (ha k x hx)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [LinearMap.map_smul_of_tower]
    exact smul_mem _ r hx

omit [NumberField K] [FiniteDimensional ℂ E] in
/-- Orthogonal complex subspaces are orthogonal over `ℝ`. -/
theorem orth_real (hV : Pairwise fun v w => V v ⟂ V w) :
    Pairwise fun v w => (V v).restrictScalars ℝ ⟂ (V w).restrictScalars ℝ := fun _ _ h =>
  isOrtho_iff_inner_eq.2 fun x hx y hy => by rw [real_inner_eq_re_inner ℂ, (hV h).inner_eq hx hy, map_zero]

/-- **Compatible**: if `E` is the orthogonal sum of the `V v`, a real subspace stable under `O_K` is the sum of its
parts at the places. -/
theorem iSup_inf_eq (hV : Pairwise fun v w => V v ⟂ V w) (htop : ⨆ v, V v = ⊤) {U : Submodule ℝ E}
    (hU : ∀ k : 𝓞 K, ∀ x ∈ U, act V (emb (k : K)) x ∈ U) : ⨆ v, U ⊓ (V v).restrictScalars ℝ = U := by
  refine le_antisymm (iSup_le fun v => inf_le_left) fun x hx => ?_
  have hx' : x ∈ iSup V := by
    rw [htop]
    exact mem_top
  rw [← (OrthogonalFamily.of_pairwise hV).sum_projection_of_mem_iSup x hx']
  exact sum_mem fun v _ => mem_iSup_of_mem v ⟨starProjection_mem hU v hx, starProjection_apply_mem (V v) x⟩

/-- **Equal dimensions**: at any two places `v₀` and `v`, the span of a stable discrete subgroup `a` has at least the
dimension at `v` that it has at `v₀`. Take `x_i ∈ a`, `d` of them, whose parts at `v₀` form a complex basis of the part
of `span a` there. Their `O_K`-span has rank `d·[K:ℚ] = 2d·n_∞`, as `Σ c_i x_i` has part `Σ σ_{v₀}(c_i) x_{i,v₀}` at
`v₀`. At each place, its part lies in the complex span of the `x_{i,w}`, of real dimension at most `2d`, and the parts
add up to at least the whole; so at `v` it has dimension `2d`. -/
theorem finrank_inf_le [IsTotallyComplex K] (hV : Pairwise fun v w => V v ⟂ V w) (htop : ⨆ v, V v = ⊤)
    {a : Submodule ℤ E} [DiscreteTopology a] (ha : Stable V a) (v₀ v : Pl K) :
    finrank ℝ ↥(span ℝ (a : Set E) ⊓ (V v₀).restrictScalars ℝ) ≤
      finrank ℝ ↥(span ℝ (a : Set E) ⊓ (V v).restrictScalars ℝ) := by
  set U := span ℝ (a : Set E)
  have hU : ∀ k : 𝓞 K, ∀ x ∈ U, act V (emb (k : K)) x ∈ U := fun k x hx => span_stable ha k hx
  let pR (w : Pl K) : E →ₗ[ℝ] E := ((V w).starProjection : E →ₗ[ℂ] E).restrictScalars ℝ
  -- A complex basis `t` of the part of `U` at `v₀`, from the parts of `a`.
  obtain ⟨t, hta, hspan, hli⟩ := exists_linearIndependent ℂ ((V v₀).starProjection '' (a : Set E))
  have : Fintype t := (LinearIndependent.setFinite hli).fintype
  choose x hxa hx using fun i : t => hta i.2
  -- The part of `U` at `v₀` has dimension at most `2|t|`.
  have h0 : finrank ℝ ↥(U ⊓ (V v₀).restrictScalars ℝ) ≤ 2 * Fintype.card t := by
    have hle : U ⊓ (V v₀).restrictScalars ℝ ≤ (span ℂ t).restrictScalars ℝ := by
      rintro y ⟨hyU, hyV⟩
      have h1 := mem_map_of_mem (f := pR v₀) hyU
      rw [map_span] at h1
      have h2 := span_le_restrictScalars ℝ ℂ _ h1
      rw [← (starProjection_eq_self_iff (K := V v₀)).2 hyV, hspan]
      exact h2
    calc finrank ℝ ↥(U ⊓ (V v₀).restrictScalars ℝ) ≤ finrank ℝ ↥((span ℂ t).restrictScalars ℝ) :=
          Submodule.finrank_mono hle
      _ = 2 * finrank ℂ ↥(span ℂ t) := finrank_real_of_complex _
      _ = 2 * Fintype.card t := by rw [← finrank_span_eq_card hli, Subtype.range_coe]
  -- The `O_K`-span `R` of the `x_i`, of rank `|t|·[K:ℚ]`.
  let ψ : (t → 𝓞 K) →+ E := AddMonoidHom.mk' (fun c => ∑ i, act V (emb (c i : K)) (x i)) fun c c' => by
    simp [act_add_left, Finset.sum_add_distrib]
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : ∑ i : t, emb (c i : K) v₀ • (i : E) = 0 := by
      have := congrArg (V v₀).starProjection hc
      simpa [ψ, map_sum, starProjection_act hV, hx] using this
    funext i
    have := Fintype.linearIndependent_iff.1 hli _ h1 i
    simpa [emb] using this
  let R : Submodule ℤ E := LinearMap.range ψ.toIntLinearMap
  have hRa : R ≤ a := by
    rintro _ ⟨c, rfl⟩
    exact sum_mem fun i _ => ha (c i) (x i) (hxa i)
  have : DiscreteTopology R := discrete_of_le hRa
  have hdim : finrank ℝ ↥(span ℝ (R : Set E)) = Fintype.card (Pl K) * (2 * Fintype.card t) := by
    rw [finrank_span, LinearMap.finrank_range_of_inj (f := ψ.toIntLinearMap) hψ, Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, RingOfIntegers.rank, IsTotallyComplex.finrank]
    ring
  -- The part of `span R` at each place `w` has dimension at most `2|t|`.
  have hm (w : Pl K) : finrank ℝ ↥((span ℝ (R : Set E)).map (pR w)) ≤ 2 * Fintype.card t := by
    have hle : (span ℝ (R : Set E)).map (pR w) ≤
        (span ℂ (Set.range fun i => (V w).starProjection (x i))).restrictScalars ℝ := by
      rw [map_le_iff_le_comap, span_le]
      rintro _ ⟨c, rfl⟩
      show (V w).starProjection (ψ c) ∈ span ℂ (Set.range fun i => (V w).starProjection (x i))
      simp only [ψ, AddMonoidHom.mk'_apply, map_sum, starProjection_act hV]
      exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
    calc finrank ℝ ↥((span ℝ (R : Set E)).map (pR w))
        ≤ finrank ℝ ↥((span ℂ (Set.range fun i => (V w).starProjection (x i))).restrictScalars ℝ) :=
          Submodule.finrank_mono hle
      _ = 2 * finrank ℂ ↥(span ℂ (Set.range fun i => (V w).starProjection (x i))) := finrank_real_of_complex _
      _ ≤ 2 * Fintype.card t := Nat.mul_le_mul_left _ (finrank_range_le_card _)
  -- The parts add up to at least the whole, so each is exactly `2|t|`.
  have hsum : Fintype.card (Pl K) * (2 * Fintype.card t) ≤ ∑ w, finrank ℝ ↥((span ℝ (R : Set E)).map (pR w)) := by
    have hpR (w : Pl K) : (span ℝ (R : Set E)).map (pR w) ≤ (V w).restrictScalars ℝ :=
      map_le_iff_le_comap.2 fun y _ => starProjection_apply_mem (V w) y
    rw [← hdim, ← finrank_iSup_of_isOrtho (W := fun w => (span ℝ (R : Set E)).map (pR w))
      ((orth_real hV).mono fun w w' h => h.mono (hpR w) (hpR w'))]
    refine Submodule.finrank_mono fun y hy => ?_
    have hy' : y ∈ iSup V := by
      rw [htop]
      exact mem_top
    rw [← (OrthogonalFamily.of_pairwise hV).sum_projection_of_mem_iSup y hy']
    exact sum_mem fun w _ => mem_iSup_of_mem w (mem_map_of_mem hy)
  have hv : 2 * Fintype.card t ≤ finrank ℝ ↥((span ℝ (R : Set E)).map (pR v)) := by
    have := (Finset.sum_eq_sum_iff_of_le fun w _ => hm w).1 (le_antisymm (Finset.sum_le_sum fun w _ => hm w)
      (by simpa [Finset.sum_const, Finset.card_univ] using hsum)) v (Finset.mem_univ v)
    omega
  -- And it lies in the part of `U` at `v`.
  have hle : (span ℝ (R : Set E)).map (pR v) ≤ U ⊓ (V v).restrictScalars ℝ := by
    rw [map_le_iff_le_comap]
    intro y hy
    exact ⟨starProjection_mem hU v (span_mono hRa hy), starProjection_apply_mem (V v) y⟩
  linarith [Submodule.finrank_mono hle]

/-- **Spans of stable discrete subgroups are balanced**: their parts at the complex places all have one dimension. -/
theorem balanced [IsTotallyComplex K] (hV : Pairwise fun v w => V v ⟂ V w) (htop : ⨆ v, V v = ⊤)
    {a : Submodule ℤ E} [DiscreteTopology a] (ha : Stable V a) :
    Balanced (fun v => (V v).restrictScalars ℝ) (span ℝ (a : Set E)) := by
  intro v
  have h := finrank_iSup_of_isOrtho (W := fun w => span ℝ (a : Set E) ⊓ (V w).restrictScalars ℝ)
    ((orth_real hV).mono fun w w' h => h.mono inf_le_right inf_le_right)
  rw [iSup_inf_eq hV htop fun k x hx => span_stable ha k hx] at h
  rw [h, Finset.sum_congr rfl fun w _ => le_antisymm (finrank_inf_le hV htop ha w v) (finrank_inf_le hV htop ha v w),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ### The class of stable saturated sublattices -/

/-- Sums of stable subgroups are stable. -/
theorem Stable.sup {a b : Submodule ℤ E} (ha : Stable V a) (hb : Stable V b) : Stable V (a ⊔ b) := fun k x hx => by
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
  rw [map_add]
  exact add_mem (mem_sup_left (ha k y hy)) (mem_sup_right (hb k z hz))

/-- Saturations in a stable `Λ` of stable subgroups are stable. -/
theorem Stable.sat {Λ a : Submodule ℤ E} (hΛ : Stable V Λ) (ha : Stable V a) : Stable V (sat Λ (a : Set E)) :=
  fun k x hx => ⟨hΛ k x hx.1, span_stable ha k hx.2⟩

/-- The `O_K`-stable saturated sublattices of a stable `Λ`: a sublattice of `Sat Λ`. -/
def stableSat (V : Pl K → Submodule ℂ E) (Λ : Submodule ℤ E) (hΛ : Stable V Λ) : Sublattice (Sat Λ) where
  carrier := {a | Stable V a.1}
  supClosed' _ ha _ hb := hΛ.sat (Stable.sup ha hb)
  infClosed' _ ha _ hb k x hx := ⟨ha k x hx.1, hb k x hx.2⟩

/-- **A hermitian lattice over `O_K` is a lattice with places**: its places are the complex places of `K`, and its class
is the `O_K`-stable saturated sublattices. -/
noncomputable def placeLattice [IsTotallyComplex K] (V : Pl K → Submodule ℂ E) (hV : Pairwise fun v w => V v ⟂ V w)
    (htop : ⨆ v, V v = ⊤) (Λ : Submodule ℤ E) [DiscreteTopology Λ] (hΛ : Stable V Λ) : PlaceLattice E where
  P := Pl K
  nonempty := ⟨⟨Classical.arbitrary _, IsTotallyComplex.isComplex _⟩⟩
  V v := (V v).restrictScalars ℝ
  orth := orth_real hV
  Λ := Λ
  S := stableSat V Λ hΛ
  bot_mem k x hx := by
    rw [(mem_bot ℤ).1 hx, map_zero]
    exact zero_mem _
  top_mem := hΛ
  balanced a ha := balanced hV htop ha

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {W : Pl K → Submodule ℂ F}

/-- A map that commutes with `O_K` sends stable saturated sublattices to stable ones. -/
theorem Stable.img {Λ : Submodule ℤ E} {Λ' : Submodule ℤ F} (hΛ' : Stable W Λ') {φ : E →L[ℝ] F}
    (hφ : ∀ (k : 𝓞 K) x, φ (act V (emb (k : K)) x) = act W (emb (k : K)) (φ x)) {a : Sat Λ} (ha : Stable V a.1) :
    Stable W (EuclidLattice.img (Λ' := Λ') φ a).1 := by
  have hm : Stable W (a.1.map ((φ : E →ₗ[ℝ] F).restrictScalars ℤ)) := by
    rintro k _ ⟨x, hx, rfl⟩
    exact ⟨_, ha k x hx, hφ k x⟩
  have := hΛ'.sat hm
  rwa [map_coe] at this

/-- A map that commutes with `O_K` pulls stable saturated sublattices back to stable ones. -/
theorem Stable.preimg {Λ : Submodule ℤ E} (hΛ : Stable V Λ) {Λ' : Submodule ℤ F} {φ : E →L[ℝ] F}
    (hφ : ∀ (k : 𝓞 K) x, φ (act V (emb (k : K)) x) = act W (emb (k : K)) (φ x)) {b : Sat Λ'} (hb : Stable W b.1) :
    Stable V (EuclidLattice.preimg (Λ := Λ) φ b).1 := by
  rintro k x ⟨hxΛ, hx⟩
  refine ⟨hΛ k x hxΛ, ?_⟩
  have hx' : φ x ∈ span ℝ (b.1 : Set F) := by
    have : x ∈ span ℝ (((span ℝ (b.1 : Set F)).comap (φ : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E) := hx
    rw [span_eq] at this
    exact this
  show act V (emb (k : K)) x ∈ span ℝ (((span ℝ (b.1 : Set F)).comap (φ : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E)
  rw [span_eq]
  show φ (act V (emb (k : K)) x) ∈ span ℝ (b.1 : Set F)
  rw [hφ]
  exact span_stable hb k hx'

end HermitianLattice

namespace HermitianLattice

open Module Submodule NumberField

attribute [local instance] InnerProductSpace.complexToReal

/-- **Hermitian frames**: hermitian `O_K`-lattices `Λ ω`, mapped into one hermitian `O_K`-lattice `Λ'` by maps `φ ω`
that commute with `O_K`, with `‖φ ω x‖ ≤ e^{h ω v}‖x‖` on the part `V ω v` at each complex place, form a frame
(`SlopeFrame.Frame`) with heights averaged over the places, `h̄ ω = n_∞⁻¹ Σ_v h ω v`. -/
noncomputable def frame {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι : Type} [Fintype ι]
    {E : ι → Type} [∀ ω, NormedAddCommGroup (E ω)] [∀ ω, InnerProductSpace ℂ (E ω)]
    [∀ ω, FiniteDimensional ℂ (E ω)] (V : ∀ ω, Pl K → Submodule ℂ (E ω))
    (hV : ∀ ω, Pairwise fun v w => V ω v ⟂ V ω w) (htop : ∀ ω, ⨆ v, V ω v = ⊤) (Λ : ∀ ω, Submodule ℤ (E ω))
    [∀ ω, DiscreteTopology (Λ ω)] (hΛ : ∀ ω, Stable (V ω) (Λ ω)) {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (W : Pl K → Submodule ℂ F) (hW : Pairwise fun v w => W v ⟂ W w)
    (hWtop : ⨆ v, W v = ⊤) (Λ' : Submodule ℤ F) [DiscreteTopology Λ'] (hΛ' : Stable W Λ')
    (φ : ∀ ω, E ω →L[ℝ] F) (hφΛ : ∀ ω, ∀ x ∈ Λ ω, φ ω x ∈ Λ')
    (hφK : ∀ ω (k : 𝓞 K) x, φ ω (act (V ω) (emb (k : K)) x) = act W (emb (k : K)) (φ ω x))
    (h : ι → Pl K → ℝ) (hφ : ∀ ω v, ∀ x ∈ V ω v, ‖φ ω x‖ ≤ Real.exp (h ω v) * ‖x‖)
    (hrk : 0 < finrank ℝ (span ℝ (Λ' : Set F))) : SlopeFrame.Frame :=
  PlaceLattice.frame (fun ω => placeLattice (V ω) (hV ω) (htop ω) (Λ ω) (hΛ ω)) (placeLattice W hW hWtop Λ' hΛ') φ
    hφΛ h hφ (fun ω _ ha => hΛ'.img (hφK ω) ha) (fun ω _ hb => (hΛ ω).preimg (hφK ω) hb) hrk

end HermitianLattice

#print axioms HermitianLattice.balanced
#print axioms HermitianLattice.frame
