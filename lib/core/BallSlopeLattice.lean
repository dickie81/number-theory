import Mathlib
import EuclidLattice
import PivotSharp

/-!
# The orbit lattice as an Arakelov lattice: its slopes, and multiplication by `k`

A join of the ball conjecture (`docs/ball-conjecture.md`) with the slope language of the library's rebuild of the
proof of RH (`SlopeFrame`, `EuclidLattice`).

Under RH the orbit form `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn)·K_H(m/n)` (`BallWeil.form`) is positive definite on real
vectors (`form_pos`, from `PivotSharp.pivot_ge_rh` at the last nonzero coordinate), so it is an inner product on `ℝ^N`
(`OrbitSpace`). The integer vectors form **the truncated orbit lattice** `Λ_N = ℤw_1 + ⋯ + ℤw_N` (`OrbitSpace.lattice`),
with `⟪w_m, w_n⟫ = √(mn)·K_H(m/n)`, and its saturated sublattices form a slope lattice (`EuclidLattice.slopeLattice`)
with `deg = −log covol`.

* `deg_top`: `deg Λ_N = −½·log det G_N`, `G_N = (√(mn)·K_H(m/n))_{m,n ≤ N}`.
* `covol_ge`: along the flag `Λ_1 ⊂ Λ_2 ⊂ ⋯ ⊂ Λ_N`, every saturated `a ⊆ Λ_N` has
  `covol(a)² ≥ K_H(1)^{r₁}·c₀^{rk a − r₁}`, `r₁ = rk(a ∩ Λ_1) ≤ 1`, `c₀ = (999/1000)(2/45)(13/10) ≥ 0.0577`. So
  `det G_N ≥ K_H(1)·c₀^{N−1}` (`det_ge`).
* **The maximal slope** (`maxSlope`): `μ_max(Λ_N) = μ₁ = −½·log K_H(1)`, attained by `ℤw_1` and by no other
  sublattice of any rank: `ℤw_1` is the first step of the Harder–Narasimhan filtration of `Λ_N`. This is the lattice
  form of `PivotSharp.shortest_unique`, for sublattices of every rank and not only for vectors.
* **Multiplication by `k`** (`mulMap`, `w_n ↦ w_{kn}`, from `Λ_N` to `Λ_M`, `kN ≤ M`): `⟪kx, ky⟫ = k·⟪x, y⟫`
  (`inner_mulMap`, from `BallWeil.inter_mul`), so it has norm `√k = e^{½·log k}` (`norm_mulMapL_le`) and sends a
  saturated `a` onto a saturated sublattice with the same rank and `deg = deg a − ½·log k·rk a` (`rk_img_mul`,
  `deg_img_mul`): a similitude of height `½·log k`, and Bost's inequality for it (`bost_mul`).
* **The frame inequality** (`mul_frame`): for the words `k = 1, …, K` from `Λ_N` into `Λ_M`, the orbit lattice
  supplies Bost's inequality and the range hypothesis of `SlopeFrame.frame_inequality`, from `μ_max(Λ_N) = μ₁`.

What the frame inequality gives on the pivots. The pivots `d_k`, the squared distances of `w_k` from
`span(w_1, …, w_{k−1})`, have `deg Λ_N = −½·Σ log d_k` (Gram–Schmidt). The lower bounds `d_1 = K_H(1)`, `d_k ≥ c₀` behind `covol_ge` come
from `PivotSharp`; the frame inequality adds none. It bounds `μ(Λ_M)` from below, that is the pivots from above on
average, and only given a depth `μ_min(Λ_M) ≥ s − H` and rank spreading for the images. The images of `Λ_N` under
`k ≤ K` lie in the coordinates `kn`, `n ≤ N`, of which there are `o(KN)` when `K` and `N` grow (Erdős's multiplication
table), so the spreading constant `α` tends to `1`, and the bound is then no better than the depth it is given. For
fixed `K` its main term is `s = μ(Λ_N) − ½·log(K!)/K`, a recursion that moves `log det G_M` by `O(M)` at most, the scale
of Hadamard's `det G_M ≤ Π G_nn = M!·K_H(1)^M`, and it still needs the depth as an input.
-/

open Real Finset Module Submodule
open scoped InnerProductSpace

noncomputable section

namespace BallSlope

/-! ## The orbit form on `Fin N → ℝ` -/

/-- The orbit Gram matrix on `Fin N`: `G(i, j) = √((i+1)(j+1))·K_H((i+1)/(j+1))`. -/
def G (N : ℕ) (i j : Fin N) : ℝ := BallWeil.gram (i + 1) (j + 1)

/-- A vector on `Fin N` as a sequence supported on `1, …, N`. -/
def ext {N : ℕ} (x : Fin N → ℝ) (n : ℕ) : ℝ := if h : 1 ≤ n ∧ n ≤ N then x ⟨n - 1, by omega⟩ else 0

lemma sum_fin_eq {N : ℕ} (f : ℕ → ℝ) : ∑ i : Fin N, f (i + 1) = ∑ n ∈ Icc 1 N, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) N]
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

lemma ext_fin {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : ext x (i + 1) = x i := by
  unfold ext
  split_ifs with h
  · congr 1
  · exact absurd ⟨by omega, by omega⟩ h

lemma form_ext {N : ℕ} (x : Fin N → ℝ) :
    BallWeil.form N (ext x) = ∑ i, ∑ j, x i * x j * G N i j := by
  unfold BallWeil.form
  rw [← sum_fin_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_fin_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ext_fin, ext_fin]
  rfl


/-- The constant of `PivotSharp.pivot_ge_rh`: `c₀ = (999/1000)(2/45)(13/10) ≥ 0.0577`. -/
def c₀ : ℝ := 999 / 1000 * (2 / 45) * (13 / 10)

lemma c₀_pos : 0 < c₀ := by unfold c₀; norm_num

lemma gram_one_lt_c₀ : BallWeil.gram 1 1 < c₀ := by
  have := PivotSharp.gram_one_lt
  unfold c₀
  linarith

lemma form_one (y : ℕ → ℝ) : BallWeil.form 1 y = y 1 ^ 2 * BallWeil.gram 1 1 := by
  unfold BallWeil.form
  simp only [Finset.Icc_self, Finset.sum_singleton]
  ring

/-- **The top coefficient of a real vector** (RH): if `y_n = 0` for `k < n ≤ N`, then `Q_N(y) ≥ g_k·y_k²`, with
`g_1 = K_H(1)` and `g_k = c₀` for `k ≥ 2`. -/
lemma form_ge_top (hRH : RiemannHypothesis) {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) (y : ℕ → ℝ)
    (h : ∀ n, k < n → n ≤ N → y n = 0) :
    (if k = 1 then BallWeil.gram 1 1 else c₀) * y k ^ 2 ≤ BallWeil.form N y := by
  rw [BallPivot.form_of_zero_above hkN h]
  split_ifs with h1
  · subst h1
    rw [form_one]
    ring_nf
    exact le_rfl
  · exact PivotSharp.pivot_ge_rh hRH (by omega) y

/-- **Under RH the orbit form is positive definite** on real vectors. -/
theorem form_pos (hRH : RiemannHypothesis) {N : ℕ} (y : ℕ → ℝ) (h : ∃ n ∈ Icc 1 N, y n ≠ 0) :
    0 < BallWeil.form N y := by
  classical
  set S := (Icc 1 N).filter (fun n => y n ≠ 0) with hS
  obtain ⟨n₀, hn₀, hy₀⟩ := h
  have hSne : S.Nonempty := ⟨n₀, Finset.mem_filter.2 ⟨hn₀, hy₀⟩⟩
  have hkS : S.max' hSne ∈ S := Finset.max'_mem S hSne
  set k := S.max' hSne with hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hkS).1).1
  have hkN : k ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hkS).1).2
  have hyk : y k ≠ 0 := (Finset.mem_filter.1 hkS).2
  have hzero : ∀ n, k < n → n ≤ N → y n = 0 := by
    intro n hkn hnN
    by_contra hne
    have := Finset.le_max' S n (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hnN⟩, hne⟩)
    omega
  have hg : 0 < (if k = 1 then BallWeil.gram 1 1 else c₀) := by
    split_ifs
    · exact PivotSharp.gram_one_pos
    · exact c₀_pos
  exact lt_of_lt_of_le (mul_pos hg (pow_pos (abs_pos.2 hyk) 2 |>.trans_eq (sq_abs _)))
    (form_ge_top hRH hk1 hkN y hzero)

lemma G_comm (N : ℕ) (i j : Fin N) : G N i j = G N j i := BallWeil.gram_comm _ _


/-- The orbit form as a bilinear form on `Fin N → ℝ`. -/
def ip (N : ℕ) (x y : Fin N → ℝ) : ℝ := ∑ i, ∑ j, x i * y j * G N i j

lemma ip_comm (N : ℕ) (x y : Fin N → ℝ) : ip N x y = ip N y x := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [G_comm]
  ring

lemma ip_self (N : ℕ) (x : Fin N → ℝ) : ip N x x = BallWeil.form N (ext x) := (form_ext x).symm

/-! ## The orbit space -/

/-- **The orbit space** `ℝ^N` with the orbit form as inner product, `⟪δ_i, δ_j⟫ = √((i+1)(j+1))·K_H((i+1)/(j+1))`:
under RH the form is positive definite (`form_pos`). The orbit lattice is `ℤ^N` in it (`lattice`). -/
def OrbitSpace (_ : RiemannHypothesis) (N : ℕ) : Type := Fin N → ℝ

namespace OrbitSpace

variable (hRH : RiemannHypothesis) (N : ℕ)

instance : AddCommGroup (OrbitSpace hRH N) := inferInstanceAs (AddCommGroup (Fin N → ℝ))

instance : Module ℝ (OrbitSpace hRH N) := inferInstanceAs (Module ℝ (Fin N → ℝ))

/-- The inner product of the orbit space. -/
@[instance_reducible]
def core : InnerProductSpace.Core ℝ (OrbitSpace hRH N) where
  inner x y := ip N x y
  conj_inner_symm x y := by
    simp only [conj_trivial]
    exact ip_comm N y x
  re_inner_nonneg x := by
    simp only [RCLike.re_to_real]
    exact le_of_le_of_eq (BallWeil.form_nonneg hRH N _) (ip_self N x).symm
  add_left x y z := by
    show ip N (fun i => x i + y i) z = ip N x z + ip N y z
    simp only [ip, add_mul, Finset.sum_add_distrib]
  smul_left x y r := by
    show ip N (fun i => r * x i) y = r * ip N x y
    simp only [ip, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  definite x hx := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hp := form_pos hRH (N := N) (ext (x : Fin N → ℝ))
      ⟨(i : ℕ) + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by rwa [ext_fin (x : Fin N → ℝ) i]⟩
    have hx' : ip N x x = 0 := hx
    have := (ip_self N x).symm.trans hx'
    linarith

instance : NormedAddCommGroup (OrbitSpace hRH N) := (core hRH N).toNormedAddCommGroup

instance : InnerProductSpace ℝ (OrbitSpace hRH N) := InnerProductSpace.ofCore (core hRH N).toCore

instance : FiniteDimensional ℝ (OrbitSpace hRH N) := inferInstanceAs (FiniteDimensional ℝ (Fin N → ℝ))

variable {hRH N}

lemma inner_def (x y : OrbitSpace hRH N) : ⟪x, y⟫_ℝ = ip N x y := rfl

lemma norm_sq (x : OrbitSpace hRH N) : ‖x‖ ^ 2 = BallWeil.form N (ext x) := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  exact ip_self N x

variable (hRH N)

/-- The orbit vectors `w_1, …, w_N`: the coordinate vectors of the orbit space. -/
def basis : Basis (Fin N) ℝ (OrbitSpace hRH N) := Pi.basisFun ℝ (Fin N)

/-- **The truncated orbit lattice** `Λ_N = ℤw_1 + ⋯ + ℤw_N`. -/
def lattice : Submodule ℤ (OrbitSpace hRH N) := span ℤ (Set.range (basis hRH N))

instance : DiscreteTopology (lattice hRH N) := by
  unfold lattice
  infer_instance

variable {hRH N}

lemma basis_apply (i : Fin N) : (basis hRH N i : Fin N → ℝ) = Pi.single i 1 :=
  Pi.basisFun_apply ℝ (Fin N) i

lemma basis_repr (x : OrbitSpace hRH N) (i : Fin N) : (basis hRH N).repr x i = x i :=
  Pi.basisFun_repr ℝ (Fin N) x i

/-- `⟪w_i, w_j⟫ = G(i, j)`. -/
lemma inner_basis (i j : Fin N) : ⟪basis hRH N i, basis hRH N j⟫_ℝ = G N i j := by
  rw [inner_def]
  rw [basis_apply, basis_apply, ip]
  simp [Pi.single_apply]

/-- The points of the lattice are the integer vectors. -/
lemma mem_lattice (x : OrbitSpace hRH N) : x ∈ lattice hRH N ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
  rw [lattice, Basis.mem_span_iff_repr_mem]
  simp only [basis_repr, Set.mem_range, algebraMap_int_eq, eq_intCast]


lemma basis_mem_lattice (i : Fin N) : basis hRH N i ∈ lattice hRH N := subset_span ⟨i, rfl⟩

/-! ## The flag `Λ_0 ⊂ Λ_1 ⊂ ⋯ ⊂ Λ_N` -/

open EuclidLattice

/-- The first `j` indices. -/
def S (N j : ℕ) : Set (Fin N) := {i | (i : ℕ) < j}

variable (hRH N) in
/-- **The flag**: `Λ_j = ℤw_1 + ⋯ + ℤw_j`, as a saturated sublattice of `Λ_N`. -/
def flag (j : ℕ) : Sat (lattice hRH N) :=
  ⟨sat (lattice hRH N) (basis hRH N '' S N j), sat_isSat (Λ := lattice hRH N) _⟩

lemma span_flag (j : ℕ) :
    span ℝ ((flag hRH N j).1 : Set (OrbitSpace hRH N)) = span ℝ (basis hRH N '' S N j) :=
  span_sat (Λ := lattice hRH N) (by rintro _ ⟨i, _, rfl⟩; exact basis_mem_lattice i)

lemma mem_span_image {j : ℕ} {x : OrbitSpace hRH N} :
    x ∈ span ℝ (basis hRH N '' S N j) ↔ ∀ i : Fin N, j ≤ (i : ℕ) → x i = 0 := by
  rw [Basis.mem_span_image]
  constructor
  · intro h i hi
    by_contra hx
    have : i ∈ S N j := h (by rw [Finset.mem_coe, Finsupp.mem_support_iff, basis_repr]; exact hx)
    exact absurd (show (i : ℕ) < j from this) (by omega)
  · intro h i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff, basis_repr] at hi
    show (i : ℕ) < j
    by_contra hij
    exact hi (h i (by omega))

lemma mem_span_flag {j : ℕ} {x : OrbitSpace hRH N} :
    x ∈ span ℝ ((flag hRH N j).1 : Set (OrbitSpace hRH N)) ↔ ∀ i : Fin N, j ≤ (i : ℕ) → x i = 0 := by
  rw [span_flag, mem_span_image]

lemma mem_flag {j : ℕ} {x : OrbitSpace hRH N} :
    x ∈ (flag hRH N j).1 ↔ x ∈ lattice hRH N ∧ ∀ i : Fin N, j ≤ (i : ℕ) → x i = 0 := by
  show x ∈ lattice hRH N ⊓ (span ℝ (basis hRH N '' S N j)).restrictScalars ℤ ↔ _
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_span_image]

lemma flag_mono {j j' : ℕ} (h : j ≤ j') : flag hRH N j ≤ flag hRH N j' := fun _ hx =>
  mem_flag.2 ⟨(mem_flag.1 hx).1, fun i hi => (mem_flag.1 hx).2 i (h.trans hi)⟩

lemma flag_zero : flag hRH N 0 = ⊥ := by
  refine Subtype.ext (Submodule.eq_bot_iff _ |>.2 fun x hx => ?_)
  exact funext fun i => (mem_flag.1 hx).2 i (Nat.zero_le _)

lemma flag_top : flag hRH N N = ⊤ :=
  Subtype.ext (le_antisymm (flag hRH N N).2.1 fun _ hx => mem_flag.2 ⟨hx, fun i hi => absurd i.2 (by omega)⟩)

/-- A vector with integer top coordinate. -/
lemma int_coord {x : OrbitSpace hRH N} (hx : x ∈ lattice hRH N) (i : Fin N) : ∃ z : ℤ, (z : ℝ) = x i :=
  (mem_lattice x).1 hx i

/-- **The gap** (RH): if `x ∈ Λ_{j+1}` is not in `Λ_j` and `V ⊆ span Λ_j`, the projection of `x` orthogonally to `V` has
squared length at least `K_H(1)` when `j = 0`, and at least `c₀` when `j ≥ 1`: it is `y` with `y_i = 0` for `i > j` and
`y_j = x_j` a nonzero integer, and `‖y‖² = Q_{j+1}(y) ≥ g_{j+1}·y_j²` (`form_ge_top`). -/
lemma gap {j : ℕ} (V : Submodule ℝ (OrbitSpace hRH N))
    (hV : V ≤ span ℝ ((flag hRH N j).1 : Set (OrbitSpace hRH N))) {x : OrbitSpace hRH N}
    (hx : x ∈ (flag hRH N (j + 1)).1) (hxj : x ∉ (flag hRH N j).1) :
    (if j + 1 = 1 then BallWeil.gram 1 1 else c₀) ≤ ‖Vᗮ.starProjection x‖ ^ 2 := by
  obtain ⟨hxΛ, hxz⟩ := mem_flag.1 hx
  have hjN : j < N := by
    by_contra hjN
    exact hxj (mem_flag.2 ⟨hxΛ, fun i hi => absurd i.2 (by omega)⟩)
  set jj : Fin N := ⟨j, hjN⟩
  have hxjj : x jj ≠ 0 := by
    intro h0
    refine hxj (mem_flag.2 ⟨hxΛ, fun i hi => ?_⟩)
    rcases Nat.eq_or_lt_of_le hi with h | h
    · have : i = jj := Fin.ext h.symm
      rw [this]; exact h0
    · exact hxz i h
  set p := V.starProjection x
  have hp : ∀ i : Fin N, j ≤ (i : ℕ) → p i = 0 := mem_span_flag.1 (hV (V.starProjection_apply_mem x))
  set y := Vᗮ.starProjection x with hy
  have hyx : y = x - p := Submodule.starProjection_orthogonal_val x
  have hyi : ∀ i : Fin N, y i = x i - p i := fun i => by rw [hyx]; rfl
  rw [norm_sq]
  have hzero : ∀ n, j + 1 < n → n ≤ N → ext (y : Fin N → ℝ) n = 0 := by
    intro n hn hnN
    have h := ext_fin (y : Fin N → ℝ) ⟨n - 1, by omega⟩
    simp only [show n - 1 + 1 = n by omega] at h
    rw [h, hyi, hxz _ (by simp; omega), hp _ (by simp; omega), sub_zero]
  have hb := form_ge_top hRH (by omega) (by omega) (ext (y : Fin N → ℝ)) hzero
  have htop : ext (y : Fin N → ℝ) (j + 1) = x jj := by
    rw [show j + 1 = (jj : ℕ) + 1 from rfl]
    refine (ext_fin (y : Fin N → ℝ) jj).trans ?_
    rw [hyi, hp jj le_rfl, sub_zero]
  rw [htop] at hb
  obtain ⟨z, hz⟩ := int_coord hxΛ jj
  have hz0 : z ≠ 0 := by rintro rfl; exact hxjj (by rw [← hz]; simp)
  have h1 : (1 : ℝ) ≤ x jj ^ 2 := by rw [← hz]; exact PivotSharp.one_le_sq_of_ne hz0
  have hg : 0 ≤ (if j + 1 = 1 then BallWeil.gram 1 1 else c₀) := by
    split_ifs
    · exact PivotSharp.gram_one_pos.le
    · exact c₀_pos.le
  nlinarith


/-! ## Ranks along the flag -/

/-- The volume of one vector is its length. -/
lemma vol_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin 1 → E) :
    GramVolume.vol v = ‖v 0‖ := by
  rw [GramVolume.vol, Matrix.det_unique, Matrix.gram, Matrix.of_apply, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma rk_def (a : Sat (lattice hRH N)) :
    (slopeLattice (lattice hRH N)).rk a = finrank ℝ (span ℝ (a.1 : Set (OrbitSpace hRH N))) := rfl

/-- `rk Λ_{j+1} ≤ rk Λ_j + 1`. -/
lemma rk_flag_succ_le (j : ℕ) :
    (slopeLattice (lattice hRH N)).rk (flag hRH N (j + 1)) ≤ (slopeLattice (lattice hRH N)).rk (flag hRH N j) + 1 := by
  rw [rk_def, rk_def, span_flag, span_flag]
  by_cases hjN : j < N
  · set jj : Fin N := ⟨j, hjN⟩
    have hsub : basis hRH N '' S N (j + 1) ⊆ basis hRH N '' S N j ∪ {basis hRH N jj} := by
      rintro _ ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge (i : ℕ) j with h | h
      · exact Or.inl ⟨i, h, rfl⟩
      · have : i = jj := Fin.ext (le_antisymm (Nat.lt_succ_iff.1 hi) h)
        exact Or.inr (by rw [this]; rfl)
    calc finrank ℝ (span ℝ (basis hRH N '' S N (j + 1)))
        ≤ finrank ℝ (span ℝ (basis hRH N '' S N j ∪ {basis hRH N jj})) := Submodule.finrank_mono (span_mono hsub)
      _ = finrank ℝ ↥(span ℝ (basis hRH N '' S N j) ⊔ span ℝ {basis hRH N jj}) := by rw [span_union]
      _ ≤ finrank ℝ (span ℝ (basis hRH N '' S N j)) + finrank ℝ (span ℝ {basis hRH N jj}) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ = finrank ℝ (span ℝ (basis hRH N '' S N j)) + 1 := by
          rw [finrank_span_singleton ((basis hRH N).ne_zero jj)]
  · have hS : S N (j + 1) = S N j := by
      ext i
      simp only [S, Set.mem_ofPred_eq]
      omega
    rw [hS]
    omega

lemma rk_flag_zero : (slopeLattice (lattice hRH N)).rk (flag hRH N 0) = 0 := by
  rw [flag_zero]
  exact (slopeLattice (lattice hRH N)).rk_bot

lemma basis_zero_mem_flag_one (hN : 1 ≤ N) : basis hRH N ⟨0, hN⟩ ∈ (flag hRH N 1).1 :=
  mem_flag.2 ⟨basis_mem_lattice _, fun i hi => by
    show (basis hRH N ⟨0, hN⟩ : Fin N → ℝ) i = 0
    rw [basis_apply, Pi.single_apply]
    split_ifs with h
    · rw [h] at hi; simp at hi
    · rfl⟩

/-- `Λ_1 = ℤw_1` has rank one. -/
lemma rk_flag_one (hN : 1 ≤ N) : (slopeLattice (lattice hRH N)).rk (flag hRH N 1) = 1 := by
  have hle := rk_flag_succ_le (hRH := hRH) (N := N) 0
  rw [rk_flag_zero, zero_add] at hle
  have hne : (⊥ : Sat (lattice hRH N)) < flag hRH N 1 := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    have hmem := basis_zero_mem_flag_one (hRH := hRH) hN
    rw [h] at hmem
    exact (basis hRH N).ne_zero _ ((Submodule.mem_bot ℤ).1 hmem)
  have := (slopeLattice (lattice hRH N)).rk_strictMono hne
  rw [(slopeLattice (lattice hRH N)).rk_bot] at this
  omega

/-- `rk Λ_N = N`. -/
lemma rk_top : (slopeLattice (lattice hRH N)).rk ⊤ = N := by
  rw [rk_eq]
  exact (finrank_eq_card_basis ((basis hRH N).restrictScalars ℤ)).trans (Fintype.card_fin N)

/-! ## The covolume bound along the flag -/

/-- **The covolume bound** (RH): every saturated `a ⊆ Λ_N` has
`covol(a)² ≥ K_H(1)^{r₁}·c₀^{rk a − r₁}`, with `r₁ = rk(a ∩ Λ_1) ∈ {0, 1}`. By induction along the flag: `a ∩ Λ_j` has
corank at most one in `a ∩ Λ_{j+1}` (modularity of rank), and the extra basis vector projects, orthogonally to
`a ∩ Λ_j`, to a vector of squared length at least `K_H(1)` (`j = 0`) or `c₀` (`j ≥ 1`) (`gap`). -/
theorem covol_ge (j : ℕ) (a : Sat (lattice hRH N)) (ha : a ≤ flag hRH N j) :
    BallWeil.gram 1 1 ^ (slopeLattice (lattice hRH N)).rk (a ⊓ flag hRH N 1) *
      c₀ ^ ((slopeLattice (lattice hRH N)).rk a - (slopeLattice (lattice hRH N)).rk (a ⊓ flag hRH N 1)) ≤
      covol a.1 ^ 2 := by
  induction j generalizing a with
  | zero =>
    rw [flag_zero, le_bot_iff] at ha
    subst ha
    rw [bot_inf_eq, (slopeLattice (lattice hRH N)).rk_bot, covol_eq_one Sat.coe_bot]
    simp
  | succ j ih =>
    set K := a ⊓ flag hRH N j with hK
    have hKj : K ≤ flag hRH N j := inf_le_right
    have ihK := ih K hKj
    obtain ⟨n, x, hxa, hrk, -, hli, hdisj, hcov⟩ := exists_adapted (inf_le_left : K ≤ a)
    rw [← rk_eq, ← rk_eq, ← hK] at hrk
    -- `n ≤ 1`, by modularity of rank
    have hmod := rk_sup_add_rk_inf a (flag hRH N j)
    rw [← hK] at hmod
    have hsup : (slopeLattice (lattice hRH N)).rk (a ⊔ flag hRH N j) ≤ (slopeLattice (lattice hRH N)).rk (flag hRH N (j + 1)) :=
      (slopeLattice (lattice hRH N)).rk_mono (sup_le ha (flag_mono (by omega)))
    have hsucc := rk_flag_succ_le (hRH := hRH) (N := N) j
    have hn1 : n ≤ 1 := by
      omega
    have hr1K : (slopeLattice (lattice hRH N)).rk (K ⊓ flag hRH N 1) ≤ (slopeLattice (lattice hRH N)).rk K := (slopeLattice (lattice hRH N)).rk_mono inf_le_left
    have hcK := covol_pos K.1
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- `j = 0`: `K = 0` and `a ⊆ Λ_1`
      have hK0 : K = ⊥ := by rw [flag_zero, le_bot_iff] at hKj; exact hKj
      have hKc : covol K.1 = 1 := covol_eq_one (by rw [hK0]; rfl)
      have hrK : (slopeLattice (lattice hRH N)).rk K = 0 := by rw [hK0]; exact (slopeLattice (lattice hRH N)).rk_bot
      have ha1 : a ⊓ flag hRH N 1 = a := inf_eq_left.2 ha
      rw [ha1, Nat.sub_self, pow_zero, mul_one]
      rw [hKc, one_mul] at hcov
      rcases Nat.lt_or_ge n 1 with h0 | h1
      · have hn0 : n = 0 := by omega
        subst hn0
        rw [hcov, GramVolume.vol_of_isEmpty]
        have : (slopeLattice (lattice hRH N)).rk a = 0 := by omega
        rw [this]
        simp
      · have hn : n = 1 := by omega
        subst hn
        have hra : (slopeLattice (lattice hRH N)).rk a = 1 := by omega
        rw [hra, pow_one, hcov, vol_one]
        have hx0 : x 0 ∉ (flag hRH N 0).1 := by
          rw [flag_zero]
          exact fun h => hli.ne_zero 0 ((Submodule.mem_bot ℤ).1 h)
        have hg := gap (j := 0) (span ℝ (K.1 : Set (OrbitSpace hRH N)))
          (span_mono (show (K.1 : Set (OrbitSpace hRH N)) ⊆ (flag hRH N 0).1 from hKj)) (ha (hxa 0)) hx0
        simpa using hg
    · -- `j ≥ 1`: `a ∩ Λ_1 = K ∩ Λ_1`
      have hK1 : K ⊓ flag hRH N 1 = a ⊓ flag hRH N 1 := by
        rw [hK, inf_assoc, inf_eq_right.2 (flag_mono (by omega : 1 ≤ j))]
      rw [hK1] at ihK hr1K
      rcases Nat.lt_or_ge n 1 with h0 | h1
      · have hn0 : n = 0 := by omega
        subst hn0
        rw [hcov, GramVolume.vol_of_isEmpty, mul_one]
        have : (slopeLattice (lattice hRH N)).rk a = (slopeLattice (lattice hRH N)).rk K := by omega
        rw [this]
        exact ihK
      · have hn : n = 1 := by omega
        subst hn
        have hx0 : x 0 ∉ (flag hRH N j).1 := by
          intro h
          have hxK : x 0 ∈ span ℝ (K.1 : Set (OrbitSpace hRH N)) := subset_span ⟨hxa 0, h⟩
          have hxr : x 0 ∈ span ℝ (Set.range x) := subset_span ⟨0, rfl⟩
          exact hli.ne_zero 0 ((Submodule.disjoint_def.1 hdisj) _ hxK hxr)
        have hg := gap (j := j) (span ℝ (K.1 : Set (OrbitSpace hRH N)))
          (span_mono (show (K.1 : Set (OrbitSpace hRH N)) ⊆ (flag hRH N j).1 from hKj)) (ha (hxa 0)) hx0
        simp only [show ¬(j + 1 = 1) by omega, ↓reduceIte] at hg
        rw [hcov, vol_one, mul_pow]
        have hra : (slopeLattice (lattice hRH N)).rk a - (slopeLattice (lattice hRH N)).rk (a ⊓ flag hRH N 1) = ((slopeLattice (lattice hRH N)).rk K - (slopeLattice (lattice hRH N)).rk (a ⊓ flag hRH N 1)) + 1 := by omega
        rw [hra, pow_succ, ← mul_assoc]
        exact mul_le_mul ihK hg c₀_pos.le (by positivity)


/-! ## The maximal slope -/

variable (hRH N) in
/-- The slope lattice of `Λ_N`: its saturated sublattices, with `deg = −log covol` (`EuclidLattice.slopeLattice`). -/
abbrev slope : SlopeFrame.SlopeLattice (Sat (lattice hRH N)) := slopeLattice (lattice hRH N)

/-- The slope of `ℤw_1`: `μ₁ = −½·log K_H(1) ≈ 1.54`. -/
def μ₁ : ℝ := -(1 / 2) * Real.log (BallWeil.gram 1 1)

lemma deg_def (a : Sat (lattice hRH N)) : (slope hRH N).deg a = -Real.log (covol a.1) := rfl

lemma log_covol (a : Sat (lattice hRH N)) : Real.log (covol a.1) = (1 / 2) * Real.log (covol a.1 ^ 2) := by
  rw [Real.log_pow]
  push_cast
  ring

/-- **Hadamard for the orbit lattice** (RH): `covol(a)² ≥ K_H(1)^{rk a}` for every saturated `a ⊆ Λ_N`. -/
theorem covol_sq_ge (a : Sat (lattice hRH N)) : BallWeil.gram 1 1 ^ (slope hRH N).rk a ≤ covol a.1 ^ 2 := by
  have h := covol_ge N a (le_top.trans_eq flag_top.symm)
  have hr : (slope hRH N).rk (a ⊓ flag hRH N 1) ≤ (slope hRH N).rk a := (slope hRH N).rk_mono inf_le_left
  have hg := PivotSharp.gram_one_pos
  calc BallWeil.gram 1 1 ^ (slope hRH N).rk a
      = BallWeil.gram 1 1 ^ (slope hRH N).rk (a ⊓ flag hRH N 1) *
          BallWeil.gram 1 1 ^ ((slope hRH N).rk a - (slope hRH N).rk (a ⊓ flag hRH N 1)) := by
        rw [← pow_add, Nat.add_sub_cancel' hr]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le gram_one_lt_c₀.le _) (by positivity)
    _ ≤ _ := h

/-- **The maximal slope of the orbit lattice is `μ₁ = −½·log K_H(1)`** (RH): every saturated sublattice `a` of `Λ_N`
has `deg a ≤ μ₁·rk a`. -/
theorem slopeLe : (slope hRH N).SlopeLe μ₁ := fun a => by
  rw [deg_def, log_covol, μ₁]
  have h := Real.log_le_log (by positivity [PivotSharp.gram_one_pos]) (covol_sq_ge a)
  rw [Real.log_pow] at h
  linarith

/-- `covol(ℤw_1)² = ‖w_1‖² = K_H(1)`. -/
theorem covol_flag_one (hN : 1 ≤ N) : covol (flag hRH N 1).1 ^ 2 = BallWeil.gram 1 1 := by
  apply le_antisymm
  · have hv : ∀ _ : Fin 1, basis hRH N ⟨0, hN⟩ ∈ (flag hRH N 1).1 := fun _ => basis_zero_mem_flag_one hN
    have hspan : span ℝ ((flag hRH N 1).1 : Set (OrbitSpace hRH N)) ≤
        span ℝ (Set.range fun _ : Fin 1 => basis hRH N ⟨0, hN⟩) := by
      rw [span_flag]
      refine span_mono ?_
      rintro _ ⟨i, hi, rfl⟩
      have : i = ⟨0, hN⟩ := Fin.ext (by have : (i : ℕ) < 1 := hi; show (i : ℕ) = 0; omega)
      exact ⟨0, by rw [this]⟩
    have hcard : Fintype.card (Fin 1) ≤ finrank ℤ (flag hRH N 1).1 := by
      rw [← rk_eq, rk_flag_one hN, Fintype.card_fin]
    have h := covol_le hv hspan hcard
    rw [vol_one] at h
    have hn : ‖basis hRH N ⟨0, hN⟩‖ ^ 2 = BallWeil.gram 1 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_basis]
      rfl
    rw [← hn]
    exact pow_le_pow_left₀ (covol_pos _).le h 2
  · have h := covol_ge 1 (flag hRH N 1) le_rfl
    rwa [inf_idem, rk_flag_one hN, Nat.sub_self, pow_zero, mul_one, pow_one] at h

/-- `ℤw_1` has slope `μ₁`. -/
theorem deg_flag_one (hN : 1 ≤ N) : (slope hRH N).deg (flag hRH N 1) = μ₁ * (slope hRH N).rk (flag hRH N 1) := by
  rw [deg_def, log_covol, covol_flag_one hN, rk_flag_one hN, μ₁]
  push_cast
  ring

/-- **`ℤw_1` is the only sublattice of maximal slope** (RH): a nonzero saturated `a ⊆ Λ_N` with `deg a ≥ μ₁·rk a` is
`ℤw_1`. So `μ_max(Λ_N) = μ₁`, attained only at `ℤw_1`: the first step of the Harder–Narasimhan filtration of `Λ_N`. -/
theorem eq_flag_one (a : Sat (lattice hRH N)) (ha : a ≠ ⊥) (hdeg : μ₁ * (slope hRH N).rk a ≤ (slope hRH N).deg a) :
    a = flag hRH N 1 := by
  have hg := PivotSharp.gram_one_pos
  have hc := covol_pos a.1
  set r := (slope hRH N).rk a
  set r₁ := (slope hRH N).rk (a ⊓ flag hRH N 1)
  have hr : r₁ ≤ r := (slope hRH N).rk_mono inf_le_left
  have hup : covol a.1 ^ 2 ≤ BallWeil.gram 1 1 ^ r := by
    rw [deg_def, log_covol, μ₁] at hdeg
    have : Real.log (covol a.1 ^ 2) ≤ Real.log (BallWeil.gram 1 1 ^ r) := by
      rw [Real.log_pow (BallWeil.gram 1 1) r]; linarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).1 this
  have hlow := covol_ge N a (le_top.trans_eq flag_top.symm)
  have hd : r - r₁ = 0 := by
    by_contra hne
    have hlt : BallWeil.gram 1 1 ^ (r - r₁) < c₀ ^ (r - r₁) := pow_lt_pow_left₀ gram_one_lt_c₀ hg.le hne
    have hsplit : BallWeil.gram 1 1 ^ r = BallWeil.gram 1 1 ^ r₁ * BallWeil.gram 1 1 ^ (r - r₁) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    have := mul_lt_mul_of_pos_left hlt (pow_pos hg r₁)
    linarith
  have hinf : a ⊓ flag hRH N 1 = a := by
    by_contra hne
    have := (slope hRH N).rk_strictMono (lt_of_le_of_ne inf_le_left hne)
    omega
  have hle : a ≤ flag hRH N 1 := inf_eq_left.1 hinf
  have hN : 1 ≤ N := by
    by_contra hN
    have : flag hRH N 1 = ⊥ :=
      Subtype.ext (Submodule.eq_bot_iff _ |>.2 fun x _ => funext fun i => absurd i.2 (by omega))
    exact ha (le_bot_iff.1 (this ▸ hle))
  have hpos : 0 < r := by
    have := (slope hRH N).rk_strictMono (bot_lt_iff_ne_bot.2 ha)
    rwa [(slope hRH N).rk_bot] at this
  have hr1 : r ≤ 1 := rk_flag_one (hRH := hRH) hN ▸ (slope hRH N).rk_mono hle
  by_contra hne
  have := (slope hRH N).rk_strictMono (lt_of_le_of_ne hle hne)
  rw [rk_flag_one hN] at this
  omega


/-! ## The degree of `Λ_N` -/

/-- The Gram matrix of `w_1, …, w_N` is the orbit Gram matrix. -/
lemma gram_basis : Matrix.gram ℝ (basis hRH N) = Matrix.of (G N) :=
  Matrix.ext fun i j => inner_basis i j

/-- `covol Λ_N = √det G_N`. -/
theorem covol_top : covol (⊤ : Sat (lattice hRH N)).1 = √(Matrix.of (G N)).det := by
  have h := covol_eq_vol ((basis hRH N).restrictScalars ℤ)
  simp only [Basis.restrictScalars_apply] at h
  rw [GramVolume.vol, gram_basis] at h
  exact h

/-- **The Arakelov degree of `Λ_N`** is `deg Λ_N = −½·log det G_N`, with `G_N = (√(mn)·K_H(m/n))_{m,n ≤ N}`. -/
theorem deg_top : (slope hRH N).deg ⊤ = -(1 / 2) * Real.log (Matrix.of (G N)).det := by
  rw [deg_def, covol_top, Real.log_sqrt]
  · ring
  · have h := covol_pos (⊤ : Sat (lattice hRH N)).1
    rw [covol_top, Real.sqrt_pos] at h
    exact h.le

variable (hRH) in
include hRH in
/-- **The Gram determinant** (RH): `det G_N ≥ K_H(1)·c₀^{N−1}` for `N ≥ 1`, from `covol_ge` at `Λ_N` itself: the product
of the pivots `d_1 ⋯ d_N` with `d_1 = K_H(1)` and `d_k ≥ c₀` for `k ≥ 2`. -/
theorem det_ge (hN : 1 ≤ N) : BallWeil.gram 1 1 * c₀ ^ (N - 1) ≤ (Matrix.of (G N)).det := by
  have h := covol_ge N (⊤ : Sat (lattice hRH N)) (le_of_eq flag_top.symm)
  rw [top_inf_eq, rk_flag_one hN, pow_one, rk_top, covol_top] at h
  have hpos := covol_pos (⊤ : Sat (lattice hRH N)).1
  rw [covol_top, Real.sqrt_pos] at hpos
  rwa [Real.sq_sqrt hpos.le] at h

/-! ## Multiplication by `k` -/

/-- `G(km, kn) = k·G(m, n)`, from `BallWeil.inter_mul`. -/
lemma gram_mul (k m n : ℕ) : BallWeil.gram (k * m) (k * n) = k * BallWeil.gram m n := by
  have h := BallWeil.inter_mul k m n
  unfold BallWeil.inter at h
  push_cast at h
  linarith

/-- The index of `w_{k(i+1)}` in `Λ_M`, for `kN ≤ M`. -/
def idx {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (i : Fin N) : Fin M :=
  ⟨k * (i + 1) - 1, by
    have : k * ((i : ℕ) + 1) ≤ k * N := Nat.mul_le_mul_left k (by omega)
    have : 1 ≤ k * ((i : ℕ) + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega⟩

lemma idx_succ {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (i : Fin N) :
    ((idx hk hkM i : ℕ) + 1) = k * ((i : ℕ) + 1) := by
  have : 1 ≤ k * ((i : ℕ) + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  simp only [idx]
  omega

variable (hRH N) in
/-- **Multiplication by `k`**: `w_n ↦ w_{kn}`, from the orbit space of `Λ_N` to that of `Λ_M`, `kN ≤ M`. -/
def mulMap {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) : OrbitSpace hRH N →ₗ[ℝ] OrbitSpace hRH M :=
  (basis hRH N).constr ℝ fun i => basis hRH M (idx hk hkM i)

lemma mulMap_basis {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (i : Fin N) :
    mulMap hRH N hk hkM (basis hRH N i) = basis hRH M (idx hk hkM i) :=
  (basis hRH N).constr_basis ℝ _ i

lemma mulMap_apply {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (x : OrbitSpace hRH N) :
    mulMap hRH N hk hkM x = ∑ i, x i • basis hRH M (idx hk hkM i) := by
  rw [mulMap, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_apply, basis_repr]

lemma inner_eq_sum (x y : OrbitSpace hRH N) :
    ⟪x, y⟫_ℝ = ∑ i, ∑ j, x i * y j * ⟪basis hRH N i, basis hRH N j⟫_ℝ := by
  simp only [inner_basis]
  rfl

/-- **Multiplication by `k` is a similitude of ratio `√k`**: `⟪kx, ky⟫ = k·⟪x, y⟫`, since `G(km, kn) = k·G(m, n)`. -/
theorem inner_mulMap {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (x y : OrbitSpace hRH N) :
    ⟪mulMap hRH N hk hkM x, mulMap hRH N hk hkM y⟫_ℝ = k * ⟪x, y⟫_ℝ := by
  rw [mulMap_apply, mulMap_apply, inner_eq_sum (x := x), Finset.mul_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, inner_basis, inner_basis]
  simp only [G, idx_succ]
  rw [gram_mul]
  ring


/-- `‖kx‖ = √k·‖x‖`. -/
theorem norm_mulMap {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (x : OrbitSpace hRH N) :
    ‖mulMap hRH N hk hkM x‖ = √k * ‖x‖ := by
  have h := inner_mulMap hk hkM x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg _)]

variable (hRH N) in
/-- Multiplication by `k` as a continuous linear map. -/
def mulMapL {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) : OrbitSpace hRH N →L[ℝ] OrbitSpace hRH M :=
  LinearMap.toContinuousLinearMap (mulMap hRH N hk hkM)

lemma mulMapL_apply {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (x : OrbitSpace hRH N) :
    mulMapL hRH N hk hkM x = mulMap hRH N hk hkM x := rfl

lemma sqrt_eq_exp (k : ℕ) (hk : 1 ≤ k) : √(k : ℝ) = Real.exp ((1 / 2) * Real.log k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [show (1 / 2) * Real.log k = Real.log k / 2 by ring, ← Real.log_sqrt hk0.le,
    Real.exp_log (Real.sqrt_pos.2 hk0)]

/-- **Multiplication by `k` has height `½·log k`**: `‖φ_k‖ ≤ e^{(1/2)·log k} = √k`. -/
theorem norm_mulMapL_le {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) :
    ‖mulMapL hRH N hk hkM‖ ≤ Real.exp ((1 / 2) * Real.log k) := by
  rw [← sqrt_eq_exp k hk]
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => by
    rw [mulMapL_apply, norm_mulMap]

/-- Multiplication by `k` sends `Λ_N` into `Λ_M`: `w_n ↦ w_{kn}`. -/
theorem mulMap_mem {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) {x : OrbitSpace hRH N} (hx : x ∈ lattice hRH N) :
    mulMapL hRH N hk hkM x ∈ lattice hRH M := by
  have h : lattice hRH N ≤ (lattice hRH M).comap ((mulMap hRH N hk hkM).restrictScalars ℤ) :=
    span_le.2 (Set.range_subset_iff.2 fun i => by
      show mulMap hRH N hk hkM (basis hRH N i) ∈ lattice hRH M
      rw [mulMap_basis]
      exact basis_mem_lattice _)
  exact h hx

/-- **Bost's inequality for multiplication by `k`** (RH): if `μ_min(a) ≥ θ` for a saturated `a ⊆ Λ_N`, then the
saturation of `k·a` in `Λ_M` has `μ_min ≥ θ − ½·log k`. -/
theorem bost_mul {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) {a : Sat (lattice hRH N)} {θ : ℝ}
    (ha : (slope hRH N).SlopeGe a θ) :
    (slope hRH M).SlopeGe (img (mulMapL hRH N hk hkM) a) (θ - (1 / 2) * Real.log k) :=
  bost (mulMapL hRH N hk hkM) (fun _ hx => mulMap_mem hk hkM hx) (norm_mulMapL_le hk hkM) ha


/-! ## Multiplication by `k` shifts degrees by exactly `½·log k` -/

lemma idx_injective {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) : Function.Injective (idx hk hkM) := by
  intro i j h
  have hi := idx_succ hk hkM i
  have hj := idx_succ hk hkM j
  rw [h, hj] at hi
  exact Fin.ext (by have := Nat.eq_of_mul_eq_mul_left (by omega) hi; omega)

variable (hRH N) in
/-- The coordinates of `Λ_M` at the multiples of `k`: `y ↦ (y_{k(i+1)})_i`, a left inverse of `mulMap`. -/
def pull {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) : OrbitSpace hRH M →ₗ[ℝ] OrbitSpace hRH N where
  toFun y := fun i => y (idx hk hkM i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma mulMap_apply_idx {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (x : OrbitSpace hRH N) (j : Fin N) :
    (mulMap hRH N hk hkM x : Fin M → ℝ) (idx hk hkM j) = x j := by
  rw [mulMap_apply]
  have : ∀ i, ((x i • basis hRH M (idx hk hkM i) : OrbitSpace hRH M) : Fin M → ℝ) (idx hk hkM j) =
      if i = j then x j else 0 := fun i => by
    show x i * (basis hRH M (idx hk hkM i) : Fin M → ℝ) (idx hk hkM j) = _
    rw [basis_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : idx hk hkM j ≠ idx hk hkM i := fun h => hij (idx_injective hk hkM h).symm
      simp [hne, hij]
  refine (Finset.sum_apply (M := fun _ : Fin M => ℝ) (idx hk hkM j) Finset.univ
    (fun i => ((x i • basis hRH M (idx hk hkM i) : OrbitSpace hRH M) : Fin M → ℝ))).trans ?_
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma pull_mulMap {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (x : OrbitSpace hRH N) :
    pull hRH N hk hkM (mulMap hRH N hk hkM x) = x :=
  funext fun j => mulMap_apply_idx hk hkM x j

lemma mulMap_pull {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) {y : OrbitSpace hRH M}
    (hy : y ∈ LinearMap.range (mulMap hRH N hk hkM)) :
    mulMap hRH N hk hkM (pull hRH N hk hkM y) = y := by
  obtain ⟨x, rfl⟩ := hy
  rw [pull_mulMap]

lemma sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = √x ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) n), ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]

/-- The volume of `k·v` is `√k^{#v}·vol v`. -/
lemma vol_mulMap {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → OrbitSpace hRH N) :
    GramVolume.vol (fun t => mulMap hRH N hk hkM (v t)) = √(k : ℝ) ^ Fintype.card ι * GramVolume.vol v := by
  have hg : Matrix.gram ℝ (fun t => mulMap hRH N hk hkM (v t)) = (k : ℝ) • Matrix.gram ℝ v :=
    Matrix.ext fun s t => by simp only [Matrix.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, inner_mulMap]
  rw [GramVolume.vol, GramVolume.vol, hg, Matrix.det_smul, Real.sqrt_mul (by positivity), sqrt_pow' (Nat.cast_nonneg k)]

/-- The image of a saturated `a ⊆ Λ_N` is `k·a` itself: `img φ_k a ⊆ φ_k(a)`, as `Λ_M` meets the span of `φ_k(a)` only
in integer vectors whose coordinates at the multiples of `k` form a point of `a`. -/
lemma mem_img {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (a : Sat (lattice hRH N)) {y : OrbitSpace hRH M}
    (hy : y ∈ (img (Λ' := lattice hRH M) (mulMapL hRH N hk hkM) a).1) :
    pull hRH N hk hkM y ∈ a.1 ∧ mulMap hRH N hk hkM (pull hRH N hk hkM y) = y := by
  obtain ⟨hyΛ, hyspan⟩ := Submodule.mem_inf.1 hy
  have hyspan' : y ∈ span ℝ (mulMap hRH N hk hkM '' (a.1 : Set (OrbitSpace hRH N))) := hyspan
  have hrange : y ∈ LinearMap.range (mulMap hRH N hk hkM) :=
    span_le.2 (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩) hyspan'
  refine ⟨a.2.2 _ ((mem_lattice _).2 fun i => int_coord hyΛ (idx hk hkM i)) ?_, mulMap_pull hk hkM hrange⟩
  have h := Submodule.apply_mem_span_image_of_mem_span (pull hRH N hk hkM) hyspan'
  rwa [← Set.image_comp, show (pull hRH N hk hkM) ∘ (mulMap hRH N hk hkM) = id from
    funext fun x => pull_mulMap hk hkM x, Set.image_id] at h

lemma mulMap_mem_img {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (a : Sat (lattice hRH N)) {x : OrbitSpace hRH N}
    (hx : x ∈ a.1) : mulMap hRH N hk hkM x ∈ (img (Λ' := lattice hRH M) (mulMapL hRH N hk hkM) a).1 :=
  Submodule.mem_inf.2 ⟨mulMap_mem hk hkM (a.2.1 hx), subset_span ⟨x, hx, rfl⟩⟩

/-- `span(img φ_k a) = φ_k(span a)`. -/
lemma span_img {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (a : Sat (lattice hRH N)) :
    span ℝ ((img (Λ' := lattice hRH M) (mulMapL hRH N hk hkM) a).1 : Set (OrbitSpace hRH M)) =
      (span ℝ (a.1 : Set (OrbitSpace hRH N))).map (mulMap hRH N hk hkM) := by
  rw [Submodule.map_span]
  exact span_sat (Λ := lattice hRH M) (by rintro _ ⟨x, hx, rfl⟩; exact mulMap_mem hk hkM (a.2.1 hx))

/-- **Multiplication by `k` keeps ranks**: `rk(img φ_k a) = rk a`. -/
theorem rk_img_mul {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (a : Sat (lattice hRH N)) :
    (slope hRH M).rk (img (mulMapL hRH N hk hkM) a) = (slope hRH N).rk a := by
  rw [rk_def, rk_def, span_img]
  apply le_antisymm (Submodule.finrank_map_le _ _)
  have h := Submodule.finrank_map_le (pull hRH N hk hkM) ((span ℝ (a.1 : Set (OrbitSpace hRH N))).map
    (mulMap hRH N hk hkM))
  rwa [← Submodule.map_comp, show (pull hRH N hk hkM).comp (mulMap hRH N hk hkM) = LinearMap.id from
    LinearMap.ext fun x => pull_mulMap hk hkM x, Submodule.map_id] at h

/-- **Multiplication by `k` is a similitude of height `½·log k`** (RH): `covol(img φ_k a) = √k^{rk a}·covol a`. -/
theorem covol_img_mul {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (a : Sat (lattice hRH N)) :
    covol (img (Λ' := lattice hRH M) (mulMapL hRH N hk hkM) a).1 = √(k : ℝ) ^ (slope hRH N).rk a * covol a.1 := by
  set b := img (Λ' := lattice hRH M) (mulMapL hRH N hk hkM) a
  have hrk : finrank ℤ b.1 = finrank ℤ a.1 := by
    rw [← rk_eq, ← rk_eq]; exact rk_img_mul hk hkM a
  apply le_antisymm
  · -- `≤`: `k` times a basis of `a` lies in `b` and spans it
    set v := fun t => ((finBasis ℤ a.1 t : a.1) : OrbitSpace hRH N)
    have h := covol_le (M := b.1) (v := fun t => mulMap hRH N hk hkM (v t))
      (fun t => mulMap_mem_img hk hkM a (finBasis ℤ a.1 t).2) (by
        rw [span_img, ← span_basis (finBasis ℤ a.1), Submodule.map_span, ← Set.range_comp]
        rfl) (by rw [Fintype.card_fin, hrk])
    rw [vol_mulMap, Fintype.card_fin, ← covol_eq_vol (finBasis ℤ a.1)] at h
    rwa [rk_eq]
  · -- `≥`: a basis of `b` is `k` times vectors of `a` that span `a`
    set z := fun t => ((finBasis ℤ b.1 t : b.1) : OrbitSpace hRH M)
    have hz := fun t => mem_img hk hkM a (finBasis ℤ b.1 t).2
    have h := covol_le (M := a.1) (v := fun t => pull hRH N hk hkM (z t)) (fun t => (hz t).1) (by
        intro x hx
        have hx' : mulMap hRH N hk hkM x ∈ span ℝ (Set.range z) := by
          rw [span_basis (finBasis ℤ b.1), span_img]
          exact Submodule.mem_map_of_mem hx
        have := Submodule.apply_mem_span_image_of_mem_span (pull hRH N hk hkM) hx'
        rw [pull_mulMap, ← Set.range_comp] at this
        exact this) (by rw [Fintype.card_fin, hrk])
    have hv : GramVolume.vol z = GramVolume.vol (fun t => mulMap hRH N hk hkM (pull hRH N hk hkM (z t))) := by
      congr 1
      funext t
      exact ((hz t).2).symm
    rw [covol_eq_vol (finBasis ℤ b.1)]
    change _ ≤ GramVolume.vol z
    have e : finrank ℤ b.1 = (slope hRH N).rk a := hrk.trans (rk_eq a).symm
    rw [hv, vol_mulMap, Fintype.card_fin, show √(k : ℝ) ^ finrank ℤ b.1 = √(k : ℝ) ^ (slope hRH N).rk a by rw [e]]
    exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **The degree shift**: `deg(img φ_k a) = deg a − ½·log k·rk a`. -/
theorem deg_img_mul {k M : ℕ} (hk : 1 ≤ k) (hkM : k * N ≤ M) (a : Sat (lattice hRH N)) :
    (slope hRH M).deg (img (mulMapL hRH N hk hkM) a) =
      (slope hRH N).deg a - (1 / 2) * Real.log k * (slope hRH N).rk a := by
  rw [deg_def, deg_def, covol_img_mul, Real.log_mul (by positivity) (covol_pos _).ne', Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg k)]
  ring


/-! ## The frame of the multiplications -/

lemma mul_le_of_lt {K N M : ℕ} (hKM : K * N ≤ M) (ω : Fin K) : ((ω : ℕ) + 1) * N ≤ M :=
  (Nat.mul_le_mul_right N (by omega)).trans hKM

/-- **The frame inequality for the multiplications** (RH): the words `k = 1, …, K` send `Λ_N` into `Λ_M`, `KN ≤ M`, by
`w_n ↦ w_{kn}`, of heights `½·log k`. The orbit lattice discharges two hypotheses of `SlopeFrame.frame_inequality`
itself: Bost's inequality on images (`bost_mul`), and the range, since `μ_max(Λ_N) = μ₁` (`slopeLe`) and the heights
are nonnegative, so `μ_max(Λ_N) − ½·log k ≤ s + U` as soon as `μ₁ ≤ s + U`. Given the mean, depth and rank-spreading
hypotheses, `μ(Λ_M) ≥ s − α·H − β·U·log(1 + H/U)`. -/
theorem mul_frame {K N M : ℕ} (hKM : K * N ≤ M) (hM : 1 ≤ M) {s U H α β : ℝ} (hU : 0 < U) (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hrange : μ₁ ≤ s + U)
    (hmean : s * ∑ _ω : Fin K, (N : ℝ) ≤
      ∑ ω : Fin K, ((slope hRH N).deg ⊤ - (1 / 2) * Real.log ((ω : ℕ) + 1 : ℕ) * N))
    (hdepth : (slope hRH M).SlopeGe ⊤ (s - H))
    (hspread : ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ 1 → ∀ a : Fin K → Sat (lattice hRH N),
      ∑ _ω : Fin K, ((N : ℝ) - (slope hRH N).rk (a _ω)) ≤ ε' * ∑ _ω : Fin K, (N : ℝ) →
      (M : ℝ) - (slope hRH M).rk (Finset.univ.sup fun ω : Fin K =>
        img (Λ' := lattice hRH M) (mulMapL hRH N (by omega : 1 ≤ (ω : ℕ) + 1) (mul_le_of_lt hKM ω)) (a ω)) ≤
        (α + β * ε') * M) :
    s - α * H - β * U * Real.log (1 + H / U) ≤ (slope hRH M).deg ⊤ / M := by
  have hN : (slope hRH N).rk ⊤ = N := rk_top
  have hMr : (slope hRH M).rk ⊤ = M := rk_top
  have h := SlopeFrame.frame_inequality (ι := Fin K) (L := fun _ => Sat (lattice hRH N)) (fun _ => slope hRH N)
    (slope hRH M) (fun ω => img (Λ' := lattice hRH M) (mulMapL hRH N (by omega : 1 ≤ (ω : ℕ) + 1) (mul_le_of_lt hKM ω)))
    (fun ω => (1 / 2) * Real.log ((ω : ℕ) + 1 : ℕ)) (fun ω _ _ ha => bost_mul _ (mul_le_of_lt hKM ω) ha)
    supClosed (by rw [hMr]; omega) hU hH hβ (by simp only [hN]; exact hmean) (fun ω b => by
      have h := slopeLe (hRH := hRH) (N := N) b
      have hh : 0 ≤ (1 / 2) * Real.log ((ω : ℕ) + 1 : ℕ) :=
        mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (ω : ℕ) + 1)))
      have hr : (0 : ℝ) ≤ (slope hRH N).rk b := Nat.cast_nonneg _
      nlinarith) hdepth (by simp only [hN, hMr]; exact hspread)
  rwa [hMr] at h

/-- **The maximal slope of the orbit lattice** (RH): for `N ≥ 1`, every saturated sublattice of `Λ_N` has slope at
most `μ₁ = −½·log K_H(1)`, `ℤw_1` has slope `μ₁`, and it is the only nonzero sublattice with slope `μ₁`. -/
theorem maxSlope (hN : 1 ≤ N) :
    (slope hRH N).SlopeLe μ₁ ∧ (slope hRH N).rk (flag hRH N 1) = 1 ∧
      (slope hRH N).deg (flag hRH N 1) = μ₁ * (slope hRH N).rk (flag hRH N 1) ∧
      ∀ a : Sat (lattice hRH N), a ≠ ⊥ → μ₁ * (slope hRH N).rk a ≤ (slope hRH N).deg a → a = flag hRH N 1 :=
  ⟨slopeLe, rk_flag_one hN, deg_flag_one hN, eq_flag_one⟩

end OrbitSpace

end BallSlope

#print axioms BallSlope.form_pos
#print axioms BallSlope.OrbitSpace.covol_ge
#print axioms BallSlope.OrbitSpace.maxSlope
#print axioms BallSlope.OrbitSpace.deg_top
#print axioms BallSlope.OrbitSpace.det_ge
#print axioms BallSlope.OrbitSpace.inner_mulMap
#print axioms BallSlope.OrbitSpace.deg_img_mul
#print axioms BallSlope.OrbitSpace.bost_mul
#print axioms BallSlope.OrbitSpace.mul_frame
