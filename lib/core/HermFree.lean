import FormSlope
import ThetaChain

/-!
# Trivial stabilisers and the free diamond action

Part VII of the exact slope bound (F) for the source lattice of the forms: at step 0 of the theta chain the classes of
decorated lattices have trivial stabilisers, and the diamond group acts freely on them. The exact cut
(`FormSlopeExact`) needs both: with a nontrivial stabiliser the block of a class is `Δ_c ∩ VV^{Stab}`, and `deg Δ_c`
does not determine its degree.

**The hypothesis.** The level group `Λ ≤ Π_{w ∈ SG} GL_n(O_E/w)` is unipotent at `w` (`UniAt`) if `(h_w − 1)^n = 0`
for every `h ∈ Λ`. The theorems ask for two places `w₀, w₁ ∈ SG` and primes `p₀ ≠ p₁` with `p_i ∈ w_i`, and for `Λ`
unipotent at both. At step 0, `Λ = uniUT` is unipotent at every place (`uniAt_uniUT`): its elements are upper
unitriangular (`uni_of_mem_uniUT`), and such a matrix is unipotent by Cayley–Hamilton (`sub_one_pow_eq_zero`). `SG`
has places over the distinct primes `g₀` and `g₁`.

**Main results.**
* F1, Minkowski at `w` (`act_eq_self_of_minkowski`): `δ ∈ GL_n(E)` keeping a finitely generated `N`, with
  `(δ − 1)N ⊆ w·N`, `δ^m = 1` and `m ∉ w`, is the identity on `N`.
* F2, the `p`-power trick (`pow_char_pow_eq_one`, `uniAt_pow`): in characteristic `p`,
  `(1 + Y)^{p^a} = 1 + Y^{p^a}`, so `h_w^{p^a} = 1` once `p^a ≥ n`.
* F3, two primes (`fst_eq_one_of_smul_eq_dia`): if `g·d = dia_a d` for a good point `d` and `g = (γ, h)`, then
  `γ = 1`.
* F4, the free action (`eq_one_of_smul_eq_dia`): then also `h = 1` and `a = 1`. Hence `Stab(c) = 1` (`stab_eq_bot`)
  for every class `c`. The diamond group `D = Π_{P ∈ ST} (O_E/P)^×` acts on the
  classes (`instMulActionDCl`: `diaCl a c = [dia_a d]` for any point `d` of `c`, `diaCl_mk`), and freely
  (`diaCl_free`).

**The route.**
* F1. Put `X = δ − 1`. If `XN ⊆ w^k N` for some `k ≥ 1`, then `δ^j − 1 − jX` maps `N` into `w^{2k} N` for every `j`,
  by induction on `j`, as `δ^{j+1} − 1 − (j+1)X = δ(δ^j − 1 − jX) + jX²`. At `j = m` it is `−mX`. As `w` is maximal
  and `m ∉ w`, `1 = um + i` with `i ∈ w`, so `XN ⊆ w^{2k} N + w·w^k N ⊆ w^{k+1} N`. Hence `XN ⊆ ⋂_k w^k N`, which is
  `0` by Krull's intersection theorem, as `N` is finitely generated (`eq_zero_of_mem_pow_smul`).
* F3. `g^k·d = dia_{a^k} d` (`pow_smul_eq_dia`), so `γ^k N = N` and `be_w ∘ γ^k = h_w^k·be_w` on `N`
  (`be_of_smul_eq_dia`). `γ` lies in the stabiliser of the unimodular `N` in `U_n(E)`, which is finite
  (`finite_stabU`), so it has finite order `p^e·m` with `p ∤ m`. For `k = p^{e+n}`, `h_w^k = 1` (F2), so
  `be_w(γ^k x − x) = 0` and `(γ^k − 1)N ⊆ w·N`, the kernel of `be_w`. Also `(γ^k)^m = 1` and `m ∉ w`
  (`natCast_not_mem`). F1 makes `γ^k` the identity on `N`, so `γ^k = 1`, as `N` spans `E^n` (`eq_one_of_act_eq`):
  this is `exists_pow_eq_one`. So the order of `γ` divides a power of `p₀` and a power of `p₁`, and is `1`.
* F4. With `γ = 1`, `h_w` fixes `(O_E/w)^n`, the image of `be_w`. And `f_P = a_P·f_P` (`f_of_smul_eq_dia`) with
  `f_P(x) ≠ 0` for some `x`, in the domain `O_E/P`.
-/

namespace HermClasses

open NumberField IsDedekindDomain Matrix HermForms ThetaChain

noncomputable section

/-! ### Unitriangular matrices are unipotent -/

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem diag_mul_of_upper {A B : Matrix (Fin n) (Fin n) R} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)]
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

/-- An upper unitriangular matrix is unipotent: `(M − 1)^n = 0`, by Cayley–Hamilton, as
`charpoly M = (X − 1)^n`. -/
theorem sub_one_pow_eq_zero {M : Matrix (Fin n) (Fin n) R} (hM : M.BlockTriangular id) (hd : ∀ i, M i i = 1) :
    (M - 1) ^ n = 0 := by
  have h := aeval_self_charpoly M
  rw [charpoly_of_isUpperTriangular M hM] at h
  simpa [hd, Finset.prod_const] using h

/-- **F2** (the `p`-power trick): in characteristic `p`, a unipotent `M` has `M^{p^a} = 1` once `p^a ≥ n`, as
`(1 + Y)^{p^a} = 1 + Y^{p^a}` (`add_pow_char_pow_of_commute`). -/
theorem pow_char_pow_eq_one {p : ℕ} [Fact p.Prime] [CharP R p] {M : Matrix (Fin n) (Fin n) R}
    (hM : (M - 1) ^ n = 0) {a : ℕ} (ha : n ≤ p ^ a) : M ^ p ^ a = 1 := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact Subsingleton.elim _ _
  · have := add_pow_char_pow_of_commute p a (Commute.one_left (M - 1))
    rwa [add_sub_cancel, one_pow, pow_eq_zero_of_le ha hM, add_zero] at this

end Uni

/-! ### The level group -/

section Level

variable {E : Type} [Field E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

/-- The level group `Λ` is **unipotent at `w ∈ SG`**: `(h_w − 1)^n = 0` for every `h ∈ Λ`. -/
def UniAt (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (w : SG) : Prop :=
  ∀ h ∈ Λ, ((h w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) - 1) ^ n = 0

/-- The elements of `uniUT` are upper unitriangular at every `w`: the unitriangular matrices are closed under
products and inverses. -/
theorem uni_of_mem_uniUT {g : ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)} (hg : g ∈ uniUT SG n) (w : SG) :
    (g w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).BlockTriangular id ∧
      ∀ i, (g w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) i i = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx w
  | one => exact ⟨blockTriangular_one, fun i => one_apply_eq i⟩
  | mul x y _ _ hx hy =>
    simp only [Pi.mul_apply, Units.val_mul]
    exact ⟨hx.1.mul hy.1, fun i => by rw [diag_mul_of_upper hx.1 hy.1, hx.2, hy.2, one_mul]⟩
  | inv x _ hx =>
    let := (x w).invertible
    have hinv : ((x w)⁻¹ : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)).val.BlockTriangular id := by
      rw [coe_units_inv]; exact blockTriangular_inv_of_blockTriangular hx.1
    refine ⟨hinv, fun i => ?_⟩
    have := congrFun (congrFun (Units.mul_inv (x w)) i) i
    rwa [diag_mul_of_upper hx.1 hinv, hx.2, one_mul, one_apply_eq] at this

/-- **Step 0**: the unitriangular level group `uniUT` is unipotent at every `w ∈ SG`. -/
theorem uniAt_uniUT (w : SG) : UniAt (uniUT SG n) w := fun _ hh =>
  sub_one_pow_eq_zero (uni_of_mem_uniUT hh w).1 (uni_of_mem_uniUT hh w).2

/-- `O_E/w` has characteristic `p` if `p ∈ w`. -/
theorem charP_residue {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 E)} (hpw : (p : 𝓞 E) ∈ w.asIdeal) :
    CharP (𝓞 E ⧸ w.asIdeal) p :=
  (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hpw)

/-- **F2 at `w`**: if `Λ` is unipotent at `w` and `p ∈ w`, then `h_w^{p^a} = 1` for `h ∈ Λ` once `p^a ≥ n`. -/
theorem uniAt_pow {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} {w : SG} (hu : UniAt Λ w) {p : ℕ}
    (hp : p.Prime) (hpw : (p : 𝓞 E) ∈ w.1.asIdeal) {h : ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)} (hh : h ∈ Λ)
    {a : ℕ} (ha : n ≤ p ^ a) : h w ^ p ^ a = 1 := by
  have := charP_residue hp hpw
  have : Fact p.Prime := ⟨hp⟩
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact pow_char_pow_eq_one (hu h hh) ha)

/-- `m ∉ w` for `m` prime to `p ∈ w`. -/
theorem natCast_not_mem {p m : ℕ} (hp : p.Prime) (hm : ¬p ∣ m) {w : HeightOneSpectrum (𝓞 E)}
    (hpw : (p : 𝓞 E) ∈ w.asIdeal) : (m : 𝓞 E) ∉ w.asIdeal := fun hmw => by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).map
    (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at huv
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ add_mem (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hmw)))

end Level

/-! ### Minkowski's lemma at a place -/

section Minkowski

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/-- **Krull's intersection theorem** for a finitely generated `N ⊂ E^n`: `⋂_k w^k N = 0` for `w ≠ O_E`. -/
theorem eq_zero_of_mem_pow_smul {N : Submodule (𝓞 E) (Fin n → E)} (hN : N.FG) {w : Ideal (𝓞 E)} (hw : w ≠ ⊤)
    {x : Fin n → E} (hx : x ∈ N) (h : ∀ k, x ∈ w ^ k • N) : x = 0 := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  have hx' : (⟨x, hx⟩ : N) ∈ (⨅ k : ℕ, w ^ k • ⊤ : Submodule (𝓞 E) N) :=
    Submodule.mem_iInf _ |>.2 fun k => (Submodule.mem_smul_top_iff _ N _).2 (h k)
  have h0 : (⨅ k : ℕ, w ^ k • ⊤ : Submodule (𝓞 E) N) = ⊥ :=
    w.iInf_pow_smul_eq_bot_of_isTorsionFree hw
  rw [h0, Submodule.mem_bot] at hx'
  exact congrArg Subtype.val hx'

/-- **F1 (Minkowski at `w`)**: let `δ ∈ GL_n(E)` keep a finitely generated `N`, with `(δ − 1)N ⊆ w·N` for a maximal
`w`, and `δ^m = 1` with `m ∉ w`. Then `δ` is the identity on `N`. With `X = δ − 1`: if `XN ⊆ w^k N` (`k ≥ 1`), then
`δ^j − 1 − jX` maps `N` into `w^{2k} N` for every `j` (induction on `j`: it moves by `δ(…) + jX²`), so at `j = m`,
`mXN ⊆ w^{2k} N`; and `1 = um + i` with `i ∈ w` gives `XN ⊆ w^{k+1} N`. So `XN ⊆ ⋂_k w^k N = 0`. -/
theorem act_eq_self_of_minkowski {N : Submodule (𝓞 E) (Fin n → E)} (hN : N.FG) {w : Ideal (𝓞 E)}
    (hw : w.IsMaximal) {δ : GL (Fin n) E} (hδ : ∀ x ∈ N, act δ x ∈ N) (h1 : ∀ x ∈ N, act δ x - x ∈ w • N)
    {m : ℕ} (hm : δ ^ m = 1) (hmw : (m : 𝓞 E) ∉ w) {x : Fin n → E} (hx : x ∈ N) : act δ x = x := by
  set X : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := act δ - LinearMap.id
  have hX (y : Fin n → E) : X y = act δ y - y := rfl
  have hδJ (J : Ideal (𝓞 E)) {y : Fin n → E} (hy : y ∈ J • N) : act δ y ∈ J • N := by
    have : act δ y ∈ (J • N).map (act δ) := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl (Submodule.map_le_iff_le_comap.2 fun z hz => hδ z hz) this
  have hXN {y : Fin n → E} (hy : y ∈ N) : X y ∈ N := N.sub_mem (hδ y hy) hy
  have key : ∀ k : ℕ, ∀ y ∈ N, X y ∈ w ^ (k + 1) • N := by
    intro k
    induction k with
    | zero => intro y hy; rw [zero_add, pow_one]; exact h1 y hy
    | succ k ih =>
      intro y hy
      have hXI {z : Fin n → E} (hz : z ∈ w ^ (k + 1) • N) : X z ∈ (w ^ (k + 1) * w ^ (k + 1)) • N := by
        have : X z ∈ (w ^ (k + 1) • N).map X := Submodule.mem_map_of_mem hz
        have hle : N.map X ≤ w ^ (k + 1) • N := Submodule.map_le_iff_le_comap.2 fun z hz => ih z hz
        rw [Submodule.map_smul''] at this
        rw [Submodule.mul_smul]
        exact Submodule.smul_mono le_rfl hle this
      have hT : ∀ j : ℕ, act (δ ^ j) y - y - (j : 𝓞 E) • X y ∈ (w ^ (k + 1) * w ^ (k + 1)) • N := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have e : act (δ ^ (j + 1)) y - y - ((j + 1 : ℕ) : 𝓞 E) • X y =
              act δ (act (δ ^ j) y - y - (j : 𝓞 E) • X y) + (j : 𝓞 E) • X (X y) := by
            simp only [pow_succ', act_mul, hX, map_sub, map_smul, Nat.cast_succ, add_smul, one_smul, smul_sub]
            abel
          rw [e]
          exact add_mem (hδJ _ ihj) (Submodule.smul_mem _ _ (hXI (ih y hy)))
      have hm' : (m : 𝓞 E) • X y ∈ (w ^ (k + 1) * w ^ (k + 1)) • N := by
        have := hT m
        rwa [hm, act_one, sub_self, zero_sub, neg_mem_iff] at this
      obtain ⟨u, i, hi, hui⟩ := hw.exists_inv hmw
      have hII : w ^ (k + 1) * w ^ (k + 1) ≤ w ^ (k + 1 + 1) := by
        rw [← pow_add]; exact Ideal.pow_le_pow_right (by omega)
      have e : X y = u • ((m : 𝓞 E) • X y) + i • X y := by rw [smul_smul, ← add_smul, hui, one_smul]
      rw [e]
      refine add_mem (Submodule.smul_mem _ _ (Submodule.smul_mono_left hII hm')) ?_
      rw [pow_succ', Submodule.mul_smul]
      exact Submodule.smul_mem_smul hi (ih y hy)
  have : X x = 0 := eq_zero_of_mem_pow_smul hN hw.ne_top (hXN hx) fun k => by
    cases k with
    | zero => simpa using hXN hx
    | succ k => exact key k x hx
  exact sub_eq_zero.1 this

end Minkowski

/-! ### One place: the order of `γ` is a power of `p` -/

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} {g : Grp E n SG Λ}
  {a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ} {d : Deco E n ST SG}

/-- `g·d = dia_a d` gives `g^k·d = dia_{a^k} d`, as `dia` commutes with `𝒢` (`dia_smul`). -/
theorem pow_smul_eq_dia (h : g • d = dia a d) (k : ℕ) : g ^ k • d = dia (a ^ k) d := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul, dia_one]
  | succ k ih => rw [pow_succ, mul_smul, h, ← dia_smul, ih, dia_dia, ← pow_succ']

omit [NumberField E] [IsCMField E] in
/-- Equal decorated lattices have equal level structures, read at a common vector. -/
theorem be_congr {d d' : Deco E n ST SG} (h : d = d') (w : SG) {x : Fin n → E} (hx : x ∈ d.N) (hx' : x ∈ d'.N) :
    d.be w ⟨x, hx⟩ = d'.be w ⟨x, hx'⟩ := by
  subst h; rfl

omit [NumberField E] [IsCMField E] in
/-- Equal decorated lattices have equal level-`T` decorations, read at a common vector. -/
theorem f_congr {d d' : Deco E n ST SG} (h : d = d') (P : ST) {x : Fin n → E} (hx : x ∈ d.N) (hx' : x ∈ d'.N) :
    d.f P ⟨x, hx⟩ = d'.f P ⟨x, hx'⟩ := by
  subst h; rfl

/-- If `g·d = dia_a d`, then `γ = g.1` keeps `N`. -/
theorem act_mem_of_smul_eq_dia (h : g • d = dia a d) {x : Fin n → E} (hx : x ∈ d.N) : act g.1.1 x ∈ d.N := by
  have : act g.1.1 x ∈ (g • d).N := Submodule.mem_map_of_mem hx
  rw [h] at this
  exact this

/-- If `g·d = dia_a d` with `g = (γ, h)`, then `be_w(γx) = h_w·be_w(x)` on `N`. -/
theorem be_of_smul_eq_dia (h : g • d = dia a d) (w : SG) {x : Fin n → E} (hx : x ∈ d.N) :
    d.be w ⟨act g.1.1 x, act_mem_of_smul_eq_dia h hx⟩ = mv (E := E) (g.2.1 w) (d.be w ⟨x, hx⟩) := by
  calc d.be w ⟨act g.1.1 x, _⟩ = (dia a d).be w ⟨act g.1.1 x, act_mem_of_smul_eq_dia h hx⟩ := rfl
    _ = (g • d).be w ⟨act g.1.1 x, Submodule.mem_map_of_mem hx⟩ := (be_congr h w _ _).symm
    _ = _ := by rw [smul_be]; congr 2; exact Subtype.ext (act_inv_act _ _)

/-- If `g·d = dia_a d` with `g = (γ, h)`, then `f_P(x) = a_P·f_P(γx)` on `N`. -/
theorem f_of_smul_eq_dia (h : g • d = dia a d) (P : ST) {x : Fin n → E} (hx : x ∈ d.N) :
    d.f P ⟨x, hx⟩ = (a P : 𝓞 E ⧸ P.1.asIdeal) • d.f P ⟨act g.1.1 x, act_mem_of_smul_eq_dia h hx⟩ := by
  calc d.f P ⟨x, hx⟩ = (g • d).f P ⟨act g.1.1 x, Submodule.mem_map_of_mem hx⟩ := by
        rw [smul_f]; congr 1; exact Subtype.ext (act_inv_act _ _).symm
    _ = (dia a d).f P ⟨act g.1.1 x, act_mem_of_smul_eq_dia h hx⟩ := f_congr h P _ _
    _ = _ := rfl

/-- `δ ∈ GL_n(E)` fixing a unimodular `N` pointwise is `1`: `N` spans `E^n`. -/
theorem eq_one_of_act_eq {N : Submodule (𝓞 E) (Fin n → E)} (hN : IsUnimodular N) {δ : GL (Fin n) E}
    (h : ∀ x ∈ N, act δ x = x) : δ = 1 := by
  refine Units.ext (toLin'.injective ?_)
  rw [Units.val_one, toLin'_one]
  exact LinearMap.ext_on (span_eq_top_of_unimodular hN) fun x hx => by simpa using h x hx

/-- **F3 at one place** (F1 with F2): if `g·d = dia_a d` for a good `d`, `Λ` is unipotent at `w` and `p ∈ w`, then
`γ^{p^e} = 1` for some `e`. `γ` has finite order `p^e·m` with `p ∤ m` (`finite_stabU`). For `k = p^{e+n}`,
`δ = γ^k` is `≡ 1` mod `w` (F2: `h_w^k = 1`, so `be_w(δx) = be_w(x)`) and `δ^m = 1`, so `δ = 1` by F1. -/
theorem exists_pow_eq_one (hd : d.Good) (h : g • d = dia a d) {w : SG} (hu : UniAt Λ w) {p : ℕ} (hp : p.Prime)
    (hpw : (p : 𝓞 E) ∈ w.1.asIdeal) : ∃ e, g.1 ^ p ^ e = 1 := by
  have := isLattice_of_unimodular hd.unimod
  have hfin := finite_stabU _ hd.unimod
  have hN (k : ℕ) : d.N.map (act (g.1 ^ k).1) = d.N := congrArg Deco.N (pow_smul_eq_dia h k)
  have hord : orderOf g.1 ≠ 0 := fun h0 => by
    obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun k : ℕ => (⟨g.1 ^ k, hN k⟩ : {γ : U E n // d.N.map (act γ.1) = d.N}))
    exact hij ((pow_inj_iff_of_orderOf_eq_zero h0).1 (congrArg Subtype.val hf))
  obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord p hp.ne_one
  refine ⟨e + n, ?_⟩
  set k := p ^ (e + n)
  have hk : n ≤ k := (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos (by omega))
  have hδN (x : Fin n → E) (hx : x ∈ d.N) : act (g.1 ^ k).1 x ∈ d.N :=
    act_mem_of_smul_eq_dia (pow_smul_eq_dia h k) hx
  have h1 (x : Fin n → E) (hx : x ∈ d.N) : act (g.1 ^ k).1 x - x ∈ w.1.asIdeal • d.N := by
    have hb := be_of_smul_eq_dia (pow_smul_eq_dia h k) w hx
    have hhk : (g ^ k).2.1 w = 1 := by
      show (g.2.1 w) ^ k = 1
      exact uniAt_pow hu hp hpw g.2.2 hk
    rw [hhk] at hb
    refine ((hd.be_ker w ⟨_, d.N.sub_mem (hδN x hx) hx⟩).1 ?_)
    rw [show (⟨act (g.1 ^ k).1 x - x, d.N.sub_mem (hδN x hx) hx⟩ : d.N) =
      ⟨act (g.1 ^ k).1 x, hδN x hx⟩ - ⟨x, hx⟩ from rfl, map_sub, sub_eq_zero]
    exact hb.trans (by simp)
  have hδm : ((g.1 ^ k).1) ^ m = 1 := by
    rw [← SubgroupClass.coe_pow, ← pow_mul, ← OneMemClass.coe_one (U E n)]
    congr 1
    rw [← orderOf_dvd_iff_pow_eq_one, hem]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (by omega)) dvd_rfl
  have hδ := eq_one_of_act_eq hd.unimod fun x hx =>
    act_eq_self_of_minkowski (fg_of_unimodular hd.unimod) inferInstance hδN h1 hδm (natCast_not_mem hp hm hpw) hx
  exact Subtype.ext hδ

end Free

/-! ### The diamond operators on classes -/

section DiaCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}

/-- **The diamond operators on classes**: `dia_a c = [dia_a d]` for the representative `d` of `c`. -/
def diaCl (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (c : DCl E n ST Λ) : DCl E n ST Λ :=
  Quotient.mk _ (diaPt a c.out)

/-- `dia_a [d] = [dia_a d]` at every point `d` of the class, as `dia` commutes with `𝒢` (`diaPt_smul`). -/
theorem diaCl_mk (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (x : points (E := E) (n := n) (ST := ST) Λ) :
    diaCl a (Quotient.mk _ x : DCl E n ST Λ) = Quotient.mk _ (diaPt a x) := by
  obtain ⟨g, hg⟩ := exists_smul_out (c := (Quotient.mk _ x : DCl E n ST Λ)) rfl
  show Quotient.mk _ (diaPt a (Quotient.mk _ x : DCl E n ST Λ).out) = _
  conv_rhs => rw [← hg, diaPt_smul]
  exact (Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g))).symm

/-- `dia_1` is the identity on classes. -/
theorem diaCl_one (c : DCl E n ST Λ) : diaCl 1 c = c := by
  rw [diaCl, diaPt_one, Quotient.out_eq]

/-- `dia_a ∘ dia_b = dia_{ab}` on classes. -/
theorem diaCl_diaCl (a b : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (c : DCl E n ST Λ) :
    diaCl a (diaCl b c) = diaCl (a * b) c := by
  show diaCl a (Quotient.mk _ (diaPt b c.out)) = _
  rw [diaCl_mk, diaPt_diaPt]
  rfl

/-- **The diamond group `D = Π_{P ∈ ST} (O_E/P)^×` acts on the classes**, by `diaCl`. -/
instance instMulActionDCl : MulAction (∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (DCl E n ST Λ) where
  smul := diaCl
  one_smul := diaCl_one
  mul_smul a b c := (diaCl_diaCl a b c).symm

end DiaCl

/-! ### Two places of distinct residue characteristics: the free action -/

section Two

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} {g : Grp E n SG Λ}
  {a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ} {d : Deco E n ST SG}

variable (w₀ w₁ : SG) {p₀ p₁ : ℕ} (hp₀ : p₀.Prime) (hp₁ : p₁.Prime) (hp : p₀ ≠ p₁) (h₀ : (p₀ : 𝓞 E) ∈ w₀.1.asIdeal)
  (h₁ : (p₁ : 𝓞 E) ∈ w₁.1.asIdeal) (hu₀ : UniAt Λ w₀) (hu₁ : UniAt Λ w₁)
include hp₀ hp₁ hp h₀ h₁ hu₀ hu₁

/-- **F3 (two primes)**: if `g·d = dia_a d` for a good `d`, then `γ = 1`: the order of `γ` divides a power of `p₀`
and a power of `p₁` (`exists_pow_eq_one`). -/
theorem fst_eq_one_of_smul_eq_dia (hd : d.Good) (h : g • d = dia a d) : g.1 = 1 := by
  obtain ⟨e₀, he₀⟩ := exists_pow_eq_one hd h hu₀ hp₀ h₀
  obtain ⟨e₁, he₁⟩ := exists_pow_eq_one hd h hu₁ hp₁ h₁
  have hc : Nat.Coprime (p₀ ^ e₀) (p₁ ^ e₁) := Nat.Coprime.pow _ _ ((Nat.coprime_primes hp₀ hp₁).2 hp)
  rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← hc.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he₀) (orderOf_dvd_of_pow_eq_one he₁)

/-- **F4 (the free action)**: for a good point `d`, `g·d = dia_a d` forces `g = 1` and `a = 1`. `γ = 1` by F3;
then `h_w·be_w = be_w` with `be_w` onto, so `h = 1`; and `a_P·f_P = f_P ≠ 0` into the domain `O_E/P`, so `a = 1`. -/
theorem eq_one_of_smul_eq_dia (hd : d.Good) (h : g • d = dia a d) : g = 1 ∧ a = 1 := by
  have hγ := fst_eq_one_of_smul_eq_dia w₀ w₁ hp₀ hp₁ hp h₀ h₁ hu₀ hu₁ hd h
  have hx1 {x : Fin n → E} (hx : x ∈ d.N) :
      (⟨act g.1.1 x, act_mem_of_smul_eq_dia h hx⟩ : d.N) = ⟨x, hx⟩ :=
    Subtype.ext (show act g.1.1 x = x by rw [hγ]; exact act_one x)
  have hh : g.2 = 1 := by
    refine Subtype.ext (funext fun w => Units.ext (toLin'.injective (LinearMap.ext fun v => ?_)))
    obtain ⟨x, rfl⟩ := hd.be_surj w v
    have hb := be_of_smul_eq_dia h w x.2
    rw [hx1 x.2] at hb
    simpa [toLin'_apply] using hb.symm
  refine ⟨Prod.ext hγ hh, funext fun P => Units.ext ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, d.f P x ≠ 0 := not_forall.1 fun hc => hd.f_ne P (LinearMap.ext hc)
  have hf := f_of_smul_eq_dia h P x.2
  rw [hx1 x.2, smul_eq_mul] at hf
  exact mul_right_cancel₀ hx (hf.symm.trans (one_mul _).symm)

/-- **Trivial stabilisers**: `Stab(c) = 1` for every class (F4 with `a = 1`). -/
theorem stab_eq_bot (c : DCl E n ST Λ) : stab c = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hg => (eq_one_of_smul_eq_dia w₀ w₁ hp₀ hp₁ hp h₀ h₁ hu₀ hu₁ c.out.2
    ((congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hg)).trans (dia_one _).symm)).1

/-- **The diamond action on classes is free**: `dia_a c = c` forces `a = 1` (F4). -/
theorem diaCl_free {c : DCl E n ST Λ} (h : diaCl a c = c) : a = 1 := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact (h.trans (Quotient.out_eq c).symm))
  exact (eq_one_of_smul_eq_dia w₀ w₁ hp₀ hp₁ hp h₀ h₁ hu₀ hu₁ c.out.2 (congrArg Subtype.val hg)).2

end Two

end

end HermClasses
