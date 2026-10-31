import ShortSieveBoxes
import ShortSieveThin

/-!
# Tuples of primes cut out by log-linear conditions

A sieve term, once its rough cofactor is written as a tuple of primes (`ShortSieveExpand.card_expand`),
counts the tuples `g : ι → ℕ` of primes with `∏ g` in the interval and with finitely many conditions
`Σ_j e_j log g_j ≤ b` (`LAtom`): the bounds of a cell, the order of the primes, the size of a product. This module
proves its asymptotic formula from the grouped Type II estimate (`ShortSieveGroup`):

* the grid `⌊a r^i⌋₊` (`grid`), whose consecutive points are within ratio `r²` (`nextG_grid_le`), and its boxes,
  in which every number has its box as index (`idxG_eq`);
* `pin`: **pinning a coordinate.** If `Σ e_j t_j` is within `D₁` of `b` and `Σ t_j` within `D₂` of `T`, then for
  `u ≠ v` with `e_u ≠ e_v`, `t_u` is within `(D₁ + |e_v| D₂)/|e_u − e_v|` of a function of the coordinates other
  than `u`, `v`. A box that straddles a condition has every tuple with product in `(x − x^{1−ρ}, x]` pinned this way,
  so that `ShortSieveThin.card_thin_le` bounds the straddling boxes.
-/

open Finset Real Filter

namespace ShortSieveTerm

open ShortSieveBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The grid -/

/-- The grid `⌊a r^i⌋₊`, `i ≤ I`. -/
noncomputable def grid (a r : ℝ) (I : ℕ) : Finset ℕ := (range (I + 1)).image fun i => ⌊a * r ^ i⌋₊

theorem card_grid_le (a r : ℝ) (I : ℕ) : (grid a r I).card ≤ I + 1 :=
  card_image_le.trans (card_range _).le

theorem mem_grid {a r : ℝ} {I e : ℕ} : e ∈ grid a r I ↔ ∃ i ≤ I, ⌊a * r ^ i⌋₊ = e := by
  simp only [grid, mem_image, mem_range, Nat.lt_succ_iff]

/-- The grid's points are at most its top `⌊a r^I⌋₊`, for `a ≥ 0` and `r ≥ 1`. -/
theorem le_top_of_mem_grid {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r) {I e : ℕ} (he : e ∈ grid a r I) :
    e ≤ ⌊a * r ^ I⌋₊ := by
  obtain ⟨i, hi, rfl⟩ := mem_grid.1 he
  exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hi) ha)

/-- **Consecutive points of the grid.** For `1 < r ≤ 2` and `a(r − 1) ≥ 2`, a grid point `e` with a point above it
has `nextG e ≤ r² e`. -/
theorem nextG_grid_le {a r : ℝ} {I : ℕ} (hr : 1 < r) (hr2 : r ≤ 2) (ha : 2 ≤ a * (r - 1)) {e : ℕ}
    (he : e ∈ grid a r I) (htop : ∃ e' ∈ grid a r I, e < e') :
    (nextG (grid a r I) e : ℝ) ≤ r ^ 2 * e := by
  have ha0 : 0 < a := by nlinarith
  obtain ⟨i, hi, rfl⟩ := mem_grid.1 he
  have hiI : i < I := by
    by_contra h
    have hiI : i = I := le_antisymm hi (not_lt.1 h)
    subst hiI
    obtain ⟨e', he', hlt⟩ := htop
    exact absurd (le_top_of_mem_grid ha0.le hr.le he') (not_le.2 hlt)
  have ht0 : a ≤ a * r ^ i := le_mul_of_one_le_right ha0.le (one_le_pow₀ hr.le)
  set t : ℝ := a * r ^ i with ht
  have hnext : ⌊a * r ^ (i + 1)⌋₊ ∈ grid a r I := mem_grid.2 ⟨i + 1, hiI, rfl⟩
  have hstep : a * r ^ (i + 1) = r * t := by rw [ht, pow_succ]; ring
  have hgap : t + 1 ≤ r * t := by nlinarith
  have hlt : ⌊t⌋₊ < ⌊a * r ^ (i + 1)⌋₊ := by
    rw [hstep]
    have h1 : ⌊t + 1⌋₊ ≤ ⌊r * t⌋₊ := Nat.floor_le_floor hgap
    rw [Nat.floor_add_one (by positivity)] at h1
    omega
  obtain ⟨-, -, hmin⟩ := nextG_spec ⟨_, hnext, hlt⟩
  have h1 : (nextG (grid a r I) ⌊t⌋₊ : ℝ) ≤ ⌊a * r ^ (i + 1)⌋₊ := by exact_mod_cast hmin _ hnext hlt
  have h2 : (⌊a * r ^ (i + 1)⌋₊ : ℝ) ≤ r * t := by rw [hstep]; exact Nat.floor_le (by positivity)
  have h3 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have h4 : (1 : ℝ) ≤ ⌊t⌋₊ * (r - 1) := by nlinarith
  calc (nextG (grid a r I) ⌊t⌋₊ : ℝ) ≤ r * t := h1.trans h2
    _ ≤ r * (⌊t⌋₊ + 1) := by nlinarith
    _ ≤ r * (r * ⌊t⌋₊) := by nlinarith
    _ = r ^ 2 * ⌊t⌋₊ := by ring

/-! ### Boxes -/

/-- In a box `(e, nextG e]`, every number has index `e`. -/
theorem idxG_eq {G : Finset ℕ} {e p : ℕ} (he : e ∈ G) (hep : e < p) (hpn : p ≤ nextG G e) : idxG G p = e := by
  obtain ⟨hmem, hlt⟩ := idxG_mem ⟨e, he, hep⟩
  have h1 : e ≤ idxG G p := le_idxG he hep
  by_contra hne
  have h2 : e < idxG G p := lt_of_le_of_ne h1 (Ne.symm hne)
  obtain ⟨-, -, hmin⟩ := nextG_spec ⟨_, hmem, h2⟩
  have := hmin _ hmem h2
  omega

/-- The box of `e` is empty unless a point of `G` lies above `e`. -/
theorem exists_above_of_lt {G : Finset ℕ} {e p : ℕ} (hep : e < p) (hpn : p ≤ nextG G e) :
    ∃ e' ∈ G, e < e' := by
  by_contra h
  have hne : ¬ (G.filter (e < ·)).Nonempty := by
    rintro ⟨e', he'⟩
    exact h ⟨e', (mem_filter.1 he').1, (mem_filter.1 he').2⟩
  rw [nextG, dite_eq_right hne] at hpn
  omega

/-- The tuples of the boxes of `J`. -/
noncomputable def full (G : Finset ℕ) (J : ι → ℕ) : Finset (ι → ℕ) :=
  ShortSieveTypeII.tuples J fun j => nextG G (J j)

theorem mem_full {G : Finset ℕ} {J g : ι → ℕ} :
    g ∈ full G J ↔ ∀ j, J j < g j ∧ g j ≤ nextG G (J j) ∧ (g j).Prime := by
  simp only [full, ShortSieveTypeII.tuples, Fintype.mem_piFinset, ShortSieveTypeII.box, mem_filter, mem_Ioc,
    and_assoc]

/-- A tuple of the boxes of `J`, with `J` on the grid, has index `J`. -/
theorem idx_eq_of_mem_full {G : Finset ℕ} {J g : ι → ℕ} (hJ : ∀ j, J j ∈ G) (hg : g ∈ full G J) :
    (fun j => idxG G (g j)) = J := by
  funext j
  obtain ⟨h1, h2, -⟩ := mem_full.1 hg j
  exact idxG_eq (hJ j) h1 h2

/-! ### Pinning a coordinate -/

/-- A sum over a finite type splits into the coordinates other than `u`, `v`, and `u`, `v`. -/
theorem sum_split {u v : ι} (huv : u ≠ v) (f : ι → ℝ) :
    ∑ j, f j = (∑ j : {j : ι // j ≠ u ∧ j ≠ v}, f j) + (f u + f v) := by
  rw [← sum_filter_add_sum_filter_not univ (fun j => j ≠ u ∧ j ≠ v)]
  congr 1
  · exact sum_subtype _ (fun j => by simp) f
  · have e : univ.filter (fun j : ι => ¬ (j ≠ u ∧ j ≠ v)) = {u, v} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      tauto
    rw [e, sum_pair huv]

/-- **Pinning a coordinate.** If `|Σ e_j t_j − b| ≤ D₁` and `|Σ t_j − T| ≤ D₂`, then for `u ≠ v` with `e_u ≠ e_v`,
`t_u` is within `(D₁ + |e_v| D₂)/|e_u − e_v|` of `(b − e_v T − Σ_{j ≠ u,v} (e_j − e_v) t_j)/(e_u − e_v)`. -/
theorem pin {u v : ι} (huv : u ≠ v) (e t : ι → ℝ) (heuv : e u ≠ e v) {b T D₁ D₂ : ℝ}
    (h1 : |∑ j, e j * t j - b| ≤ D₁) (h2 : |∑ j, t j - T| ≤ D₂) :
    |t u - (b - e v * T - ∑ j : {j : ι // j ≠ u ∧ j ≠ v}, (e j - e v) * t j) / (e u - e v)| ≤
      (D₁ + |e v| * D₂) / |e u - e v| := by
  have hne : e u - e v ≠ 0 := sub_ne_zero.2 heuv
  rw [sum_split huv] at h1 h2
  set R := {j : ι // j ≠ u ∧ j ≠ v}
  set δ₁ := (∑ j : R, e j * t j) + (e u * t u + e v * t v) - b with hδ₁
  set δ₂ := (∑ j : R, t j) + (t u + t v) - T with hδ₂
  have hR : ∑ j : R, (e j - e v) * t j = ∑ j : R, e j * t j - e v * ∑ j : R, t j := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  have key : t u - (b - e v * T - ∑ j : R, (e j - e v) * t j) / (e u - e v) = (δ₁ - e v * δ₂) / (e u - e v) := by
    rw [hR, hδ₁, hδ₂]
    field_simp
    ring
  rw [key, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc |δ₁ - e v * δ₂| ≤ |δ₁| + |e v * δ₂| := abs_sub _ _
    _ = |δ₁| + |e v| * |δ₂| := by rw [abs_mul]
    _ ≤ D₁ + |e v| * D₂ := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))

/-! ### Log-linear conditions and their boundaries -/

/-- A log-linear condition on a tuple `g : ι → ℕ`: `Σ e_j log g_j ≤ b(x)`, or `< b(x)` when `strict`. -/
structure LAtom (ι : Type*) where
  e : ι → ℝ
  b : ℝ → ℝ
  strict : Bool

/-- The value `Σ e_j log g_j`. -/
noncomputable def LAtom.val (A : LAtom ι) (g : ι → ℕ) : ℝ := ∑ j, A.e j * Real.log (g j)

/-- The condition holds at `g`. -/
def LAtom.Holds (A : LAtom ι) (x : ℝ) (g : ι → ℕ) : Prop :=
  if A.strict then A.val g < A.b x else A.val g ≤ A.b x

/-- The tuples of primes in `[x^c, x²)` within `D` of the condition's boundary, with product in
`(x − x^{1−ρ}, x]`. -/
noncomputable def near (c ρ D : ℝ) (A : LAtom ι) (x : ℝ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι => SieveRough.primesIn (x ^ c) (x ^ (2 : ℝ))).filter fun g =>
    |A.val g - A.b x| ≤ D ∧ x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x

/-- **The boundary of a condition is thin.** For a condition with `e_u ≠ e_v` for some `u ≠ v`, `0 < c ≤ 1`,
`12ρ < c` and `D ≥ 0`: the tuples within `D` of its boundary with product in `(x − x^{1−ρ}, x]` number at most
`C x^{1−ρ}/log² x`. The coordinate `u` is pinned (`pin`, with `|Σ log g_j − log x| ≤ log 2`) to an interval of ratio
`K = exp(2δ')` around a function of the coordinates other than `u`, `v`, and `ShortSieveThin.card_thin_le` counts
such tuples. -/
theorem card_near_le {c ρ D : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hD : 0 ≤ D)
    (A : LAtom ι) {u v : ι} (huv : u ≠ v) (he : A.e u ≠ A.e v) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x → ((near c ρ D A x).card : ℝ) ≤ C * x ^ (1 - ρ) / Real.log x ^ 2 := by
  set δ' : ℝ := (D + |A.e v| * Real.log 2) / |A.e u - A.e v| with hδ'
  have hδ'0 : 0 ≤ δ' := by positivity
  set K : ℝ := Real.exp (2 * δ') with hK
  have hK1 : 1 ≤ K := Real.one_le_exp (by positivity)
  obtain ⟨C, x₁, hC0, hC⟩ := ShortSieveThin.card_thin_le ι hc hc1 hK1 hρ hρc
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop hρ).eventually_ge_atTop (2 : ℝ))
  refine ⟨C, max (max x₁ x₂) 2, hC0, fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxρ : 2 ≤ x ^ ρ := hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  -- the pinned interval, as a function of the coordinates other than `u`, `v`
  set L : ({j : ι // j ≠ u ∧ j ≠ v} → ℕ) → ℝ := fun h =>
    (A.b x - A.e v * Real.log x - ∑ j : {j : ι // j ≠ u ∧ j ≠ v}, (A.e j - A.e v) * Real.log (h j)) /
      (A.e u - A.e v) with hL
  set X : ({j : ι // j ≠ u ∧ j ≠ v} → ℕ) → ℝ := fun h => Real.exp (L h - δ') with hX
  refine le_trans ?_ (hC x hx1 u v huv X)
  refine Nat.cast_le.2 (card_le_card fun g hg => ?_)
  obtain ⟨hgQ, hval, hp1, hp2⟩ := mem_filter.1 hg
  have hgpos : ∀ j, 0 < g j := fun j =>
    (SieveRough.mem_primesIn.1 (Fintype.mem_piFinset.1 hgQ j)).1.pos
  -- `|Σ log g_j − log x| ≤ log 2`
  have hy : x ^ (1 - ρ) ≤ x / 2 := by
    have e : x ^ (1 - ρ) = x / x ^ ρ := by rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [e]; exact div_le_div_of_nonneg_left hx0.le (by norm_num) hxρ
  have hprod : ((∏ j, g j : ℕ) : ℝ) = ∏ j, (g j : ℝ) := by push_cast; rfl
  have hP0 : 0 < ∏ j, (g j : ℝ) := prod_pos fun j _ => by exact_mod_cast hgpos j
  have hlogP : Real.log (∏ j, (g j : ℝ)) = ∑ j, Real.log (g j) :=
    Real.log_prod fun j _ => by exact_mod_cast (hgpos j).ne'
  have h2 : |∑ j, Real.log (g j) - Real.log x| ≤ Real.log 2 := by
    rw [← hlogP, ← Real.log_div hP0.ne' hx0.ne', abs_le]
    rw [hprod] at hp1 hp2
    constructor
    · rw [neg_le, ← Real.log_inv, Real.log_le_log_iff (by positivity) (by positivity)]
      rw [inv_div, div_le_iff₀ hP0]; linarith
    · calc Real.log ((∏ j, (g j : ℝ)) / x) ≤ Real.log 1 :=
            Real.log_le_log (div_pos hP0 hx0) (by rw [div_le_one hx0]; exact hp2)
        _ = 0 := Real.log_one
        _ ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : |∑ j, A.e j * Real.log (g j) - A.b x| ≤ D := hval
  have hpin := pin huv A.e (fun j => Real.log (g j)) he h1 h2
  have hpin' : |Real.log (g u) - L (fun j => g j)| ≤ δ' := hpin
  obtain ⟨hlo, hhi⟩ := abs_le.1 hpin'
  have hgu : (0 : ℝ) < g u := by exact_mod_cast hgpos u
  refine mem_filter.2 ⟨hgQ, ?_, ?_, by rw [← hprod]; exact hp1, by rw [← hprod]; exact hp2⟩
  · -- `exp(L − δ') ≤ g_u`
    rw [hX]
    calc Real.exp (L (fun j => g j) - δ') ≤ Real.exp (Real.log (g u)) := Real.exp_le_exp.2 (by linarith)
      _ = g u := Real.exp_log hgu
  · -- `g_u ≤ exp(2δ') exp(L − δ')`
    rw [hX, hK, ← Real.exp_add]
    calc (g u : ℝ) = Real.exp (Real.log (g u)) := (Real.exp_log hgu).symm
      _ ≤ Real.exp (2 * δ' + (L (fun j => g j) - δ')) := Real.exp_le_exp.2 (by linarith)

/-! ### Type II witnesses -/

/-- A Type II witness for tuples indexed by `ι`: `m` groups (`grp`), their lower exponents `a` and Hölder
exponents `δ`. -/
structure Wit (ι : Type*) where
  m : ℕ
  grp : ι → Fin m
  a : Fin m → ℝ
  δ : Fin m → ℝ

/-- The witness is admissible at `θ` and `κ`: `κ < a_i`, `δ_i > 0`, `Σ 1/δ_i = 1`, and `δ_i` admissible for the
moment lemmas at `D_i = (1 − θ + κ)/(a_i − κ)`. -/
def Wit.OK (w : Wit ι) (θ κ : ℝ) : Prop :=
  (∀ i, κ < w.a i) ∧ (∀ i, 0 < w.δ i) ∧ ∑ i, 1 / w.δ i = 1 ∧
    ∀ i, ShortSieveTypeII.MomentOK ((1 - θ + κ) / (w.a i - κ)) (w.δ i)

/-- The witness covers `g` with margin `μ` at `x`: each group's product is at least `x^{a_i + μ}`. -/
def Wit.Covers (w : Wit ι) (x μ : ℝ) (g : ι → ℕ) : Prop :=
  ∀ i, x ^ (w.a i + μ) ≤ ∏ j ∈ univ.filter (w.grp · = i), (g j : ℝ)

/-- **The grouped Type II estimate for a list of witnesses**, with common constants
(`ShortSieveGroup.abs_card_tuples_sub_le_group_of_pos` for each). -/
theorem typeII_uniform (W : List (Wit ι)) {c θ κ ρ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hθ : 0 < θ)
    (hρ : 0 < ρ) (hθρ : θ + ρ ≤ 1) (hW : ∀ w ∈ W, w.OK θ κ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, 0 ≤ C ∧ 1 ≤ x₀ ∧ ∀ w ∈ W, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ, x ^ θ ≤ y → y ≤ y₁ →
      y₁ ≤ x ^ (1 - ρ) → ∀ N M : ι → ℕ, (∀ j, x ^ c ≤ N j) → (∀ j, N j ≤ M j) →
        (∀ i, ∏ j ∈ univ.filter (w.grp · = i), M j ≤ 2 * ∏ j ∈ univ.filter (w.grp · = i), N j) →
        (∀ i, x ^ w.a i ≤ ∏ j ∈ univ.filter (w.grp · = i), (N j : ℝ)) →
        |(#{g ∈ ShortSieveTypeII.tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ ShortSieveTypeII.tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧
            ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤ C * y * x ^ (-η) := by
  induction W with
  | nil => exact ⟨1, one_pos, 0, 1, le_rfl, le_rfl, fun w hw => absurd hw List.not_mem_nil⟩
  | cons w W ih =>
    obtain ⟨η₂, hη₂, C₂, x₂, hC₂, hx₂, h₂⟩ := ih fun w' hw' => hW w' (List.mem_cons_of_mem _ hw')
    obtain ⟨ha, hδ, hδs, hok⟩ := hW w List.mem_cons_self
    obtain ⟨η₁, hη₁, C₁, x₁, h₁⟩ :=
      ShortSieveGroup.abs_card_tuples_sub_le_group_of_pos w.grp hc hκ ha hθ hρ hθρ hδ hδs hok
    refine ⟨min η₁ η₂, lt_min hη₁ hη₂, max (max C₁ 0) C₂, max (max x₁ 1) x₂, le_trans hC₂ (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), fun w' hw' x hx y y₁ hy hyy₁ hy₁ N M hN hNM hrat ha' => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hy0 : 0 ≤ y := le_trans (Real.rpow_nonneg (by linarith) θ) hy
    have hmono : ∀ {C' η' : ℝ}, C' ≤ max (max C₁ 0) C₂ → min η₁ η₂ ≤ η' →
        C' * y * x ^ (-η') ≤ max (max C₁ 0) C₂ * y * x ^ (-min η₁ η₂) := by
      intro C' η' hC' hη'
      have hpow : x ^ (-η') ≤ x ^ (-min η₁ η₂) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hC0 : 0 ≤ max (max C₁ 0) C₂ := le_trans (le_max_right _ _) (le_max_left _ _)
      calc C' * y * x ^ (-η') ≤ max (max C₁ 0) C₂ * y * x ^ (-η') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hy0) (by positivity)
        _ ≤ max (max C₁ 0) C₂ * y * x ^ (-min η₁ η₂) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0 hy0)
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact (h₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) y y₁ hy hyy₁ hy₁ N M hN hNM hrat
        ha').trans (hmono (le_trans (le_max_left _ _) (le_max_left _ _)) (min_le_left _ _))
    · exact (h₂ w' hw' x (le_trans (le_max_right _ _) hx) y y₁ hy hyy₁ hy₁ N M hN hNM hrat ha').trans
        (hmono (le_max_right _ _) (min_le_right _ _))

/-- **The boundaries of a list of conditions**, with common constants (`card_near_le` for each). -/
theorem near_uniform (v : ι) {c ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hρ : 0 < ρ) (hρc : 12 * ρ < c)
    (D : LAtom ι → ℝ) (hD : ∀ A, 0 ≤ D A) (atoms : List (LAtom ι)) (hatoms : ∀ A ∈ atoms, ∃ u, u ≠ v ∧ A.e u ≠ A.e v) :
    ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ A ∈ atoms, ∀ x : ℝ, x₀ ≤ x →
      ((near c ρ (D A) A x).card : ℝ) ≤ C * x ^ (1 - ρ) / Real.log x ^ 2 := by
  induction atoms with
  | nil => exact ⟨0, 0, le_rfl, fun A hA => absurd hA List.not_mem_nil⟩
  | cons A atoms ih =>
    obtain ⟨C₂, x₂, hC₂, h₂⟩ := ih fun A' hA' => hatoms A' (List.mem_cons_of_mem _ hA')
    obtain ⟨u, huv, he⟩ := hatoms A List.mem_cons_self
    obtain ⟨C₁, x₁, hC₁, h₁⟩ := card_near_le hc hc1 hρ hρc (hD A) A huv he
    refine ⟨max C₁ C₂, max (max x₁ x₂) 0, le_trans hC₁ (le_max_left _ _), fun A' hA' x hx => ?_⟩
    have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
    have hmono : ∀ {C' : ℝ}, C' ≤ max C₁ C₂ →
        C' * x ^ (1 - ρ) / Real.log x ^ 2 ≤ max C₁ C₂ * x ^ (1 - ρ) / Real.log x ^ 2 := fun hC' =>
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hx0 _)) (by positivity)
    rcases List.mem_cons.1 hA' with rfl | hA'
    · exact (h₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)).trans (hmono (le_max_left _ _))
    · exact (h₂ A' hA' x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)).trans
        (hmono (le_max_right _ _))

/-! ### Tuples in the same boxes -/

section boxes

variable {a r : ℝ} {I : ℕ} (hr : 1 < r) (hr2 : r ≤ 2) (ha : 2 ≤ a * (r - 1))
include hr hr2 ha

/-- A number in the box of a grid point `e` is at most `r² e`. -/
theorem le_of_mem_box {e p : ℕ} (he : e ∈ grid a r I) (hep : e < p) (hpn : p ≤ nextG (grid a r I) e) :
    (p : ℝ) ≤ r ^ 2 * e :=
  le_trans (by exact_mod_cast hpn) (nextG_grid_le hr hr2 ha he (exists_above_of_lt hep hpn))

/-- Two tuples in the same boxes have coordinates within ratio `r²`. -/
theorem le_of_mem_full {J g g' : ι → ℕ} (hJ : ∀ j, J j ∈ grid a r I) (hg : g ∈ full (grid a r I) J)
    (hg' : g' ∈ full (grid a r I) J) (j : ι) : (g j : ℝ) ≤ r ^ 2 * g' j := by
  obtain ⟨h1, h2, -⟩ := mem_full.1 hg j
  obtain ⟨h1', -, -⟩ := mem_full.1 hg' j
  calc (g j : ℝ) ≤ r ^ 2 * J j := le_of_mem_box hr hr2 ha (hJ j) h1 h2
    _ ≤ r ^ 2 * g' j := mul_le_mul_of_nonneg_left (by exact_mod_cast h1'.le) (by positivity)

/-- Two tuples in the same boxes have logarithms within `2 log r`. -/
theorem abs_log_sub_le {J g g' : ι → ℕ} (hJ : ∀ j, J j ∈ grid a r I) (hg : g ∈ full (grid a r I) J)
    (hg' : g' ∈ full (grid a r I) J) (j : ι) :
    |Real.log (g j) - Real.log (g' j)| ≤ 2 * Real.log r := by
  have hp : ∀ g : ι → ℕ, g ∈ full (grid a r I) J → (0 : ℝ) < g j := fun g hg => by
    exact_mod_cast (mem_full.1 hg j).2.2.pos
  have hr0 : 0 < r := by linarith
  have key : ∀ g g' : ι → ℕ, g ∈ full (grid a r I) J → g' ∈ full (grid a r I) J →
      Real.log (g j) - Real.log (g' j) ≤ 2 * Real.log r := by
    intro g g' hg hg'
    have h := le_of_mem_full hr hr2 ha hJ hg hg' j
    have := Real.log_le_log (hp g hg) h
    rw [Real.log_mul (by positivity) (hp g' hg').ne', Real.log_pow] at this
    push_cast at this
    linarith
  rw [abs_le]
  constructor
  · linarith [key g' g hg' hg]
  · exact key g g' hg hg'

/-- **A box that straddles a condition lies near its boundary.** If `A` holds at `g₀` and fails at `g'`, both in the
boxes of `J`, then every `g` in them has `|Σ e_j log g_j − b| ≤ (Σ |e_j|)·2 log r`. -/
theorem abs_val_sub_le {J g₀ g' g : ι → ℕ} (hJ : ∀ j, J j ∈ grid a r I)
    (hg₀ : g₀ ∈ full (grid a r I) J) (hg' : g' ∈ full (grid a r I) J) (hg : g ∈ full (grid a r I) J)
    (A : LAtom ι) {x : ℝ} (h₀ : A.Holds x g₀) (h' : ¬ A.Holds x g') :
    |A.val g - A.b x| ≤ (∑ j, |A.e j|) * (2 * Real.log r) := by
  have hclose : ∀ g₁ : ι → ℕ, g₁ ∈ full (grid a r I) J →
      |A.val g - A.val g₁| ≤ (∑ j, |A.e j|) * (2 * Real.log r) := by
    intro g₁ hg₁
    rw [LAtom.val, LAtom.val, ← sum_sub_distrib, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_log_sub_le hr hr2 ha hJ hg hg₁ j) (abs_nonneg _)
  have h₀' : A.val g₀ ≤ A.b x := by
    unfold LAtom.Holds at h₀
    split_ifs at h₀ with hs
    · exact h₀.le
    · exact h₀
  have h'' : A.b x ≤ A.val g' := by
    unfold LAtom.Holds at h'
    split_ifs at h' with hs
    · exact not_lt.1 h'
    · exact (not_le.1 h').le
  have c₀ := abs_le.1 (hclose g₀ hg₀)
  have c' := abs_le.1 (hclose g' hg')
  rw [abs_le]
  constructor <;> linarith [c₀.1, c₀.2, c'.1, c'.2]

end boxes

/-! ### The asymptotic formula -/

/-- The number of box tuples is negligible against a power: for `r > 1` and `η > 0`, eventually
`(⌈2 log x/log r⌉₊ + 1)^d x^{−η} ≤ 1/log² x`. -/
theorem eventually_card_pow_le {r η : ℝ} (hr : 1 < r) (hη : 0 < η) (d : ℕ) :
    ∀ᶠ x : ℝ in atTop, ((⌈2 * Real.log x / Real.log r⌉₊ + 1 : ℕ) : ℝ) ^ d * x ^ (-η) ≤ 1 / Real.log x ^ 2 := by
  have hlr : 0 < Real.log r := Real.log_pos hr
  set K₀ : ℝ := 2 / Real.log r + 2 with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop ((d : ℝ) + 2) hη).bound (c := 1 / K₀ ^ d) (by positivity)
  filter_upwards [ho, Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)]
    with x hox hlx hx1
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  -- `I + 1 ≤ K₀ log x`
  have hI : ((⌈2 * Real.log x / Real.log r⌉₊ + 1 : ℕ) : ℝ) ≤ K₀ * Real.log x := by
    push_cast
    have h1 : (⌈2 * Real.log x / Real.log r⌉₊ : ℝ) < 2 * Real.log x / Real.log r + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : 2 * Real.log x / Real.log r = 2 / Real.log r * Real.log x := by ring
    rw [hK₀]
    nlinarith
  -- `K₀^d log^{d+2} x ≤ x^η`
  have hlog : K₀ ^ d * Real.log x ^ (d + 2) ≤ x ^ η := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hox
    have e : Real.log x ^ ((d : ℝ) + 2) = Real.log x ^ (d + 2) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [e] at hox
    have := mul_le_mul_of_nonneg_left hox (pow_nonneg hK₀pos.le d)
    rwa [← mul_assoc, mul_one_div_cancel (pow_pos hK₀pos d).ne', one_mul] at this
  have hxη : x ^ (-η) * x ^ η = 1 := by rw [← Real.rpow_add hx0]; simp
  calc ((⌈2 * Real.log x / Real.log r⌉₊ + 1 : ℕ) : ℝ) ^ d * x ^ (-η) ≤ (K₀ * Real.log x) ^ d * x ^ (-η) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hI d) (by positivity)
    _ = K₀ ^ d * Real.log x ^ (d + 2) * x ^ (-η) / Real.log x ^ 2 := by
        rw [mul_pow, pow_add]; field_simp
    _ ≤ x ^ η * x ^ (-η) / Real.log x ^ 2 := by gcongr
    _ = 1 / Real.log x ^ 2 := by rw [mul_comm, hxη]

open Classical in
/-- The tuples `g : ι → ℕ` of primes in `(x^c, x²)` satisfying the conditions. -/
noncomputable def cut (c : ℝ) (atoms : List (LAtom ι)) (x : ℝ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι => (Ioo ⌊x ^ c⌋₊ ⌈x ^ (2 : ℝ)⌉₊).filter Nat.Prime).filter
    fun g => ∀ A ∈ atoms, A.Holds x g

/-- **Tuples of primes cut out by log-linear conditions.** Let `0 < c ≤ 1`, `θ, κ, ρ, μ > 0` with `12ρ < c` and
`θ + ρ ≤ 1`, a coordinate `v`, conditions each with `e_u ≠ e_v` for some `u ≠ v`, and Type II witnesses admissible
at `θ, κ`, one of which covers (with margin `μ`) every tuple of the cut with product in `(x/4, 2x]`, for large `x`.
Then for large `x` and `x^θ ≤ y ≤ x^{1−ρ}`, the tuples of the cut with product in `(x − y, x]` number
`(y/x^{1−ρ})` times those with product in `(x − x^{1−ρ}, x]`, up to `C y/log² x`.

The tuples are split by the boxes of the grid `⌊x^c r^i⌋₊`, `r = 2^{1/(2d)}` (`abs_sum_sub_le_boxes`). A box tuple
that meets the cut gets the grouped Type II estimate from the witness of one of its tuples (`typeII_uniform`): the
boxes' ratio `r²` loses at most `(r²)^d = 2` in each group's product. There are `O(log^d x)` box tuples, so their
errors `C y x^{−η}` add up to `O(y/log² x)` (`eventually_card_pow_le`). A box tuple that straddles the cut has its
tuples with product in the comparison interval near the boundary of a condition (`abs_val_sub_le`), and the
boundaries are thin (`near_uniform`); a box tuple that leaves `(x^c, x²)` has no tuple with product below `x`. -/
theorem abs_card_cut_sub_le (v : ι) {c θ κ ρ μ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hθ : 0 < θ)
    (hκ : 0 < κ) (hρ : 0 < ρ) (hρc : 12 * ρ < c) (hθρ : θ + ρ ≤ 1) (hμ : 0 < μ)
    (atoms : List (LAtom ι)) (hatoms : ∀ A ∈ atoms, ∃ u, u ≠ v ∧ A.e u ≠ A.e v)
    (W : List (Wit ι)) (hW : ∀ w ∈ W, w.OK θ κ)
    (hcov : ∀ᶠ x in atTop, ∀ g ∈ cut c atoms x, x / 4 < ∏ j, (g j : ℝ) → ∏ j, (g j : ℝ) ≤ 2 * x →
      ∃ w ∈ W, w.Covers x μ g) :
    ∃ C : ℝ, ∀ᶠ x in atTop, ∀ y : ℝ, x ^ θ ≤ y → y ≤ x ^ (1 - ρ) →
      |(#{g ∈ cut c atoms x | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
        y / x ^ (1 - ρ) * #{g ∈ cut c atoms x | x - x ^ (1 - ρ) < ((∏ j, g j : ℕ) : ℝ) ∧
          ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤ C * y / Real.log x ^ 2 := by
  classical
  set d : ℕ := Fintype.card ι with hd_def
  have hd : 0 < d := Fintype.card_pos_iff.2 ⟨v⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- the grid's ratio `r = 2^{1/(2d)}`, with `(r²)^d = 2`
  set r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (2 * d)) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  have hr2 : r ≤ 2 := by
    calc r ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          rw [div_le_one (by positivity)]; linarith)
      _ = 2 := Real.rpow_one 2
  have hrd : (r ^ 2) ^ d = 2 := by
    rw [hr, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  have hr0 : 0 < r := by linarith
  have hr21 : 1 ≤ r ^ 2 := one_le_pow₀ hr1.le
  have hlr : 0 < Real.log r := Real.log_pos hr1
  -- powers of `r²` over at most `d = #ι` coordinates
  have hpowd : ∀ s : Finset ι, (r ^ 2) ^ s.card ≤ 2 := fun s => by
    rw [← hrd]; exact pow_le_pow_right₀ hr21 (card_le_univ s)
  -- the boundaries of the conditions
  set D : LAtom ι → ℝ := fun A => (∑ j, |A.e j|) * (2 * Real.log r) with hDdef
  have hD0 : ∀ A, 0 ≤ D A := fun A => mul_nonneg (sum_nonneg fun j _ => abs_nonneg _) (by positivity)
  obtain ⟨Cn, xn, hCn, hnear⟩ := near_uniform v hc hc1 hρ hρc D hD0 atoms hatoms
  -- the Type II estimate for the witnesses
  obtain ⟨η, hη, CW, xW, hCW, hxW, hTII⟩ := typeII_uniform W (c := c / 2) (by positivity) hκ hθ hρ hθρ hW
  refine ⟨CW + atoms.length * Cn, ?_⟩
  -- the conditions on `x`
  have ev4 : ∀ᶠ x : ℝ in atTop, 2 / (r - 1) ≤ x ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop _
  have ev5 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (c / 2) := (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have ev6 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ μ := (tendsto_rpow_atTop hμ).eventually_ge_atTop _
  have ev7 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ ρ := (tendsto_rpow_atTop hρ).eventually_ge_atTop _
  filter_upwards [hcov, eventually_ge_atTop xn, eventually_ge_atTop xW, eventually_ge_atTop (3 : ℝ), ev4, ev5, ev6,
    ev7, eventually_card_pow_le hr1 hη d] with x hcovx hxn hxW' hx3 hx4 hx5 hx6 hx7 hxI
  intro y hy1 hy2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 θ) hy1
  set y₁ : ℝ := x ^ (1 - ρ) with hy₁
  have hy₁0 : 0 < y₁ := Real.rpow_pos_of_pos hx0 _
  have hy₁x : y₁ ≤ x / 2 := by
    have e : y₁ = x / x ^ ρ := by rw [hy₁, Real.rpow_sub hx0, Real.rpow_one]
    rw [e]; exact div_le_div_of_nonneg_left hx0.le (by norm_num) hx7
  have hxc0 : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
  have hxc_half : x ^ c = x ^ (c / 2) * x ^ (c / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  have ha : 2 ≤ x ^ c * (r - 1) := by
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < r - 1)).1 hx4; linarith
  -- the grid
  set I : ℕ := ⌈2 * Real.log x / Real.log r⌉₊ with hI
  set G := grid (x ^ c) r I with hG
  have hbot : ⌊x ^ c⌋₊ ∈ G := mem_grid.2 ⟨0, Nat.zero_le _, by simp⟩
  have hGge : ∀ e ∈ G, ⌊x ^ c⌋₊ ≤ e := fun e he => by
    obtain ⟨i, -, rfl⟩ := mem_grid.1 he
    exact Nat.floor_le_floor (le_mul_of_one_le_right hxc0.le (one_le_pow₀ hr1.le))
  have htop : x ^ (2 : ℝ) ≤ x ^ c * r ^ I := by
    have hrI : x ^ (2 : ℝ) ≤ r ^ I := by
      rw [← Real.exp_log (Real.rpow_pos_of_pos hx0 _), ← Real.exp_log (pow_pos hr0 I), Real.log_rpow hx0,
        Real.log_pow]
      refine Real.exp_le_exp.2 ?_
      have h := Nat.le_ceil (2 * Real.log x / Real.log r)
      rw [← hI, div_le_iff₀ hlr] at h
      linarith
    calc x ^ (2 : ℝ) ≤ r ^ I := hrI
      _ ≤ x ^ c * r ^ I := le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hx1 hc.le)
  have htopG : ⌊x ^ c * r ^ I⌋₊ ∈ G := mem_grid.2 ⟨I, le_rfl, rfl⟩
  -- the floor of `x^c` is at least `x^{c/2}`
  have hfloor : x ^ (c / 2) ≤ (⌊x ^ c⌋₊ : ℝ) := by
    have h1 : x ^ c - 1 < ⌊x ^ c⌋₊ := Nat.sub_one_lt_floor _
    nlinarith
  -- the cut's tuples lie in the boxes of their indices
  set S := cut c atoms x with hS
  have hSmem : ∀ g ∈ S, ∀ j, ⌊x ^ c⌋₊ < g j ∧ (g j : ℝ) < x ^ (2 : ℝ) ∧ (g j).Prime := by
    intro g hg j
    have h := (Fintype.mem_piFinset.1 (mem_filter.1 hg).1) j
    obtain ⟨hIoo, hp⟩ := mem_filter.1 h
    obtain ⟨h1, h2⟩ := mem_Ioo.1 hIoo
    exact ⟨h1, Nat.lt_ceil.1 h2, hp⟩
  set Js := Fintype.piFinset fun _ : ι => G with hJs
  set box : (ι → ℕ) → (ι → ℕ) := fun g j => idxG G (g j) with hbox
  have hlo : ∀ g ∈ S, ∀ j, ∃ e ∈ G, e < g j := fun g hg j => ⟨_, hbot, (hSmem g hg j).1⟩
  have hhi : ∀ g ∈ S, ∀ j, ∃ e ∈ G, g j ≤ e := fun g hg j => by
    refine ⟨_, htopG, Nat.le_floor ?_⟩
    exact ((hSmem g hg j).2.1.le).trans htop
  have hboxJs : ∀ g ∈ S, box g ∈ Js := fun g hg =>
    Fintype.mem_piFinset.2 fun j => (idxG_mem (hlo g hg j)).1
  have hfull : ∀ g ∈ S, g ∈ full G (box g) := fun g hg =>
    mem_tuples_idxG (fun j => (hSmem g hg j).2.2) (hlo g hg) (hhi g hg)
  -- the weights
  set fA : (ι → ℕ) → ℝ := fun g =>
    if x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x then 1 else 0 with hfA
  set fB : (ι → ℕ) → ℝ := fun g =>
    if x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x then 1 else 0 with hfB
  have hfA0 : ∀ g, 0 ≤ fA g := fun g => by simp only [hfA]; split_ifs <;> norm_num
  have hfB0 : ∀ g, 0 ≤ fB g := fun g => by simp only [hfB]; split_ifs <;> norm_num
  have hprodcast : ∀ g : ι → ℕ, ((∏ j, g j : ℕ) : ℝ) = ∏ j, (g j : ℝ) := fun g => by push_cast; rfl
  -- coordinates of tuples in the boxes of an index of the grid
  have hJG : ∀ J ∈ Js, ∀ j, J j ∈ G := fun J hJ j => (Fintype.mem_piFinset.1 hJ) j
  have hgt : ∀ J ∈ Js, ∀ g ∈ full G J, ∀ j, x ^ c < g j := by
    intro J hJ g hg j
    have h1 := (mem_full.1 hg j).1
    have h2 := hGge _ (hJG J hJ j)
    have h3 : x ^ c < (⌊x ^ c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊x ^ c⌋₊ : ℝ) + 1 ≤ g j := by exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt h2 h1)
    linarith
  -- the products of two tuples of the same boxes are within factor `2`
  have hprod2 : ∀ J ∈ Js, ∀ g ∈ full G J, ∀ g' ∈ full G J, ∏ j, (g j : ℝ) ≤ 2 * ∏ j, (g' j : ℝ) := by
    intro J hJ g hg g' hg'
    calc ∏ j, (g j : ℝ) ≤ ∏ j, (r ^ 2 * g' j) :=
          prod_le_prod₀ (fun j _ => by positivity) fun j _ => le_of_mem_full hr1 hr2 ha (hJG J hJ) hg hg' j
      _ = (r ^ 2) ^ d * ∏ j, (g' j : ℝ) := by rw [prod_mul_distrib, prod_const, card_univ]
      _ = 2 * ∏ j, (g' j : ℝ) := by rw [hrd]
  -- the Type II estimate on a box tuple that meets the cut
  have hE : ∀ J ∈ Js, (∃ g ∈ S, box g = J) →
      |∑ g ∈ full G J, fA g - y / y₁ * ∑ g ∈ full G J, fB g| ≤ CW * y * x ^ (-η) := by
    rintro J hJ ⟨g₀, hg₀S, hg₀J⟩
    have hg₀ : g₀ ∈ full G J := hg₀J ▸ hfull g₀ hg₀S
    simp only [hfA, hfB, sum_boole]
    by_cases hBn : ∃ g₁ ∈ full G J, x - y₁ < ((∏ j, g₁ j : ℕ) : ℝ) ∧ ((∏ j, g₁ j : ℕ) : ℝ) ≤ x
    · obtain ⟨g₁, hg₁, hB1, hB2⟩ := hBn
      rw [hprodcast] at hB1 hB2
      have hP1 := hprod2 J hJ g₀ hg₀ g₁ hg₁
      have hP2 := hprod2 J hJ g₁ hg₁ g₀ hg₀
      obtain ⟨w, hwW, hwcov⟩ := hcovx g₀ hg₀S (by linarith) (by linarith)
      have hboxne : ∀ j, ∃ e' ∈ G, J j < e' := fun j =>
        exists_above_of_lt (mem_full.1 hg₀ j).1 (mem_full.1 hg₀ j).2.1
      have hnext : ∀ j, (nextG G (J j) : ℝ) ≤ r ^ 2 * J j := fun j =>
        nextG_grid_le hr1 hr2 ha (hJG J hJ j) (hboxne j)
      refine hTII w hwW x hxW' y y₁ hy1 hy2 le_rfl J (fun j => nextG G (J j)) (fun j => ?_) (fun j => ?_)
        (fun i => ?_) (fun i => ?_)
      · exact hfloor.trans (by exact_mod_cast hGge _ (hJG J hJ j))
      · exact (nextG_spec (hboxne j)).2.1.le
      · -- `∏ nextG ≤ (r²)^{#group} ∏ J ≤ 2 ∏ J`
        have hreal : (∏ j ∈ univ.filter (w.grp · = i), (nextG G (J j) : ℝ)) ≤
            2 * ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) := by
          calc (∏ j ∈ univ.filter (w.grp · = i), (nextG G (J j) : ℝ)) ≤
                ∏ j ∈ univ.filter (w.grp · = i), (r ^ 2 * J j) :=
                prod_le_prod₀ (fun j _ => by positivity) fun j _ => hnext j
            _ = (r ^ 2) ^ (univ.filter (w.grp · = i)).card * ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) := by
                rw [prod_mul_distrib, prod_const]
            _ ≤ 2 * ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) :=
                mul_le_mul_of_nonneg_right (hpowd _) (prod_nonneg fun j _ => by positivity)
        exact_mod_cast hreal
      · -- `∏ J ≥ ∏ g₀/(r²)^{#group} ≥ x^{a+μ}/2 ≥ x^a`
        have hcovi := hwcov i
        have hg₀J' : ∀ j, (g₀ j : ℝ) ≤ r ^ 2 * J j := fun j =>
          (by exact_mod_cast (mem_full.1 hg₀ j).2.1 : (g₀ j : ℝ) ≤ nextG G (J j)).trans (hnext j)
        have hle : ∏ j ∈ univ.filter (w.grp · = i), (g₀ j : ℝ) ≤
            2 * ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) := by
          calc ∏ j ∈ univ.filter (w.grp · = i), (g₀ j : ℝ) ≤ ∏ j ∈ univ.filter (w.grp · = i), (r ^ 2 * J j) :=
                prod_le_prod₀ (fun j _ => by positivity) fun j _ => hg₀J' j
            _ = (r ^ 2) ^ (univ.filter (w.grp · = i)).card * ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) := by
                rw [prod_mul_distrib, prod_const]
            _ ≤ 2 * ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) :=
                mul_le_mul_of_nonneg_right (hpowd _) (prod_nonneg fun j _ => by positivity)
        have hxa : x ^ (w.a i + μ) = x ^ w.a i * x ^ μ := Real.rpow_add hx0 _ _
        have hxa0 : 0 < x ^ w.a i := Real.rpow_pos_of_pos hx0 _
        calc x ^ w.a i = x ^ w.a i * 2 / 2 := by ring
          _ ≤ x ^ w.a i * x ^ μ / 2 := by gcongr
          _ = x ^ (w.a i + μ) / 2 := by rw [hxa]
          _ ≤ (∏ j ∈ univ.filter (w.grp · = i), (g₀ j : ℝ)) / 2 := by gcongr
          _ ≤ ∏ j ∈ univ.filter (w.grp · = i), (J j : ℝ) := by linarith
    · push Not at hBn
      have hA0 : ∀ g ∈ full G J, ¬ (x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) := by
        rintro g hg ⟨h1, h2⟩
        exact absurd h2 (not_le.2 (hBn g hg (by linarith)))
      have hB0 : ∀ g ∈ full G J, ¬ (x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) := by
        rintro g hg ⟨h1, h2⟩
        exact absurd h2 (not_le.2 (hBn g hg h1))
      rw [filter_false_of_mem hA0, filter_false_of_mem hB0]
      simp only [card_empty, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
      positivity
  -- a coordinate is at most the product
  have hcoord : ∀ g : ι → ℕ, (∀ j, 0 < g j) → ∀ j, (g j : ℝ) ≤ ((∏ j, g j : ℕ) : ℝ) := fun g hg j => by
    exact_mod_cast Nat.le_of_dvd (prod_pos fun j _ => hg j) (dvd_prod_of_mem _ (mem_univ j))
  have hr2le : r ^ 2 ≤ 2 := by
    calc r ^ 2 ≤ (r ^ 2) ^ d := le_self_pow₀ hr21 hd.ne'
      _ = 2 := hrd
  -- a box tuple that straddles the cut has its tuples in the comparison interval near a boundary
  have hstrad : ∀ J ∈ Js, (∃ g ∈ S, box g = J) → (∃ g ∈ full G J, ¬ (g ∈ S ∧ box g = J)) →
      ∑ g ∈ full G J, fB g ≤ ∑ A ∈ atoms.toFinset, (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ) := by
    rintro J hJ ⟨g₀, hg₀S, hg₀J⟩ ⟨g', hg', hg'n⟩
    have hg₀ : g₀ ∈ full G J := hg₀J ▸ hfull g₀ hg₀S
    have hg'J : box g' = J := idx_eq_of_mem_full (hJG J hJ) hg'
    have hg'S : g' ∉ S := fun h => hg'n ⟨h, hg'J⟩
    have hpos : ∀ g ∈ full G J, ∀ j, 0 < g j := fun g hg j => (mem_full.1 hg j).2.2.pos
    simp only [hfB, sum_boole]
    by_cases hbase : ∀ j, (g' j : ℝ) < x ^ (2 : ℝ)
    · -- some condition fails at `g'`
      have hnot : ¬ ∀ A ∈ atoms, A.Holds x g' := by
        intro hall
        refine hg'S (mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j =>
          mem_filter.2 ⟨mem_Ioo.2 ⟨?_, ?_⟩, (mem_full.1 hg' j).2.2⟩, hall⟩)
        · exact lt_of_le_of_lt (hGge _ (hJG J hJ j)) (mem_full.1 hg' j).1
        · exact Nat.lt_ceil.2 (hbase j)
      push Not at hnot
      obtain ⟨A, hA, hA'⟩ := hnot
      have hA₀ : A.Holds x g₀ := (mem_filter.1 hg₀S).2 A hA
      refine le_trans ?_ (single_le_sum (f := fun A => (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ))
        (fun A _ => Nat.cast_nonneg _) (List.mem_toFinset.2 hA))
      refine Nat.cast_le.2 (card_le_card fun g hg => ?_)
      obtain ⟨hgf, hB1, hB2⟩ := mem_filter.1 hg
      refine mem_filter.2 ⟨hgf, mem_filter.2 ⟨?_,
        abs_val_sub_le hr1 hr2 ha (hJG J hJ) hg₀ hg' hgf A hA₀ hA', hB1, hB2⟩⟩
      refine Fintype.mem_piFinset.2 fun j =>
        SieveRough.mem_primesIn.2 ⟨(mem_full.1 hgf j).2.2, (hgt J hJ g hgf j).le, ?_⟩
      have hx2 : x < x ^ (2 : ℝ) := by
        rw [Real.rpow_two, sq]; exact lt_mul_of_one_lt_right hx0 (by linarith)
      exact lt_of_le_of_lt ((hcoord g (hpos g hgf) j).trans hB2) hx2
    · -- a coordinate of `g'` reaches `x²`: no tuple of these boxes has product at most `x`
      push Not at hbase
      obtain ⟨j₀, hj₀⟩ := hbase
      have hempty : (full G J).filter
          (fun g => x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x) = ∅ := by
        refine filter_eq_empty_iff.2 fun g hg hgB => ?_
        have h2 := hgB.2
        have h1 := le_of_mem_full hr1 hr2 ha (hJG J hJ) hg' hg j₀
        have h3 := hcoord g (hpos g hg) j₀
        rw [Real.rpow_two, sq] at hj₀
        have h5 : x * x ≤ 2 * x := by
          calc x * x ≤ g' j₀ := hj₀
            _ ≤ r ^ 2 * g j₀ := h1
            _ ≤ 2 * g j₀ := mul_le_mul_of_nonneg_right hr2le (by positivity)
            _ ≤ 2 * x := by linarith
        have h6 : x ≤ 2 := le_of_mul_le_mul_right h5 hx0
        linarith
      rw [hempty, card_empty, Nat.cast_zero]
      exact sum_nonneg fun A _ => Nat.cast_nonneg _
  -- the boxes are disjoint
  have hfib : ∀ N : Finset (ι → ℕ), ∑ J ∈ Js, (((full G J).filter (· ∈ N)).card : ℝ) ≤ N.card := by
    intro N
    have h1 : ∀ J ∈ Js, (full G J).filter (· ∈ N) ⊆ N.filter (fun g => box g = J) := fun J hJ g hg => by
      obtain ⟨hgf, hgN⟩ := mem_filter.1 hg
      exact mem_filter.2 ⟨hgN, idx_eq_of_mem_full (hJG J hJ) hgf⟩
    calc ∑ J ∈ Js, (((full G J).filter (· ∈ N)).card : ℝ) ≤
          ∑ J ∈ Js, ((N.filter (fun g => box g = J)).card : ℝ) :=
          sum_le_sum fun J hJ => by exact_mod_cast card_le_card (h1 J hJ)
      _ = ((N.filter fun g => box g ∈ Js).card : ℝ) := by
          exact_mod_cast sum_card_fiberwise_eq_card_filter N Js box
      _ ≤ N.card := by exact_mod_cast card_filter_le _ _
  -- the straddling box tuples
  set t : (ι → ℕ) → ℝ := fun J =>
    ∑ A ∈ atoms.toFinset, (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ) with ht
  have ht0 : ∀ J ∈ Js, 0 ≤ t J := fun J _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hT : ∑ J ∈ Js, t J ≤ atoms.length * (Cn * y₁ / Real.log x ^ 2) := by
    calc ∑ J ∈ Js, t J
        = ∑ A ∈ atoms.toFinset, ∑ J ∈ Js, (((full G J).filter (· ∈ near c ρ (D A) A x)).card : ℝ) := sum_comm
      _ ≤ ∑ A ∈ atoms.toFinset, ((near c ρ (D A) A x).card : ℝ) := sum_le_sum fun A _ => hfib _
      _ ≤ ∑ _A ∈ atoms.toFinset, Cn * y₁ / Real.log x ^ 2 :=
          sum_le_sum fun A hA => hnear A (List.mem_toFinset.1 hA) x hxn
      _ = atoms.toFinset.card * (Cn * y₁ / Real.log x ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ atoms.length * (Cn * y₁ / Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le atoms) (by positivity)
  -- the box sandwich
  have hsand := abs_sum_sub_le_boxes S Js box hboxJs (full G) hfull hfA0 hfB0 (div_nonneg hy0.le hy₁0.le)
    (by positivity : 0 ≤ CW * y * x ^ (-η)) hE t ht0 hstrad
  have hJcard : (Js.card : ℝ) ≤ ((I + 1 : ℕ) : ℝ) ^ d := by
    rw [hJs, Fintype.card_piFinset, prod_const, card_univ]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast card_grid_le _ _ _) d
  have hgA : (#{g ∈ S | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) = ∑ g ∈ S, fA g := by
    simp only [hfA, sum_boole]
  have hgB : (#{g ∈ S | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) = ∑ g ∈ S, fB g := by
    simp only [hfB, sum_boole]
  rw [hgA, hgB]
  have hlx : 0 < Real.log x ^ 2 := by
    have : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have h1 : (Js.card : ℝ) * (CW * y * x ^ (-η)) ≤ CW * y * (1 / Real.log x ^ 2) := by
    calc (Js.card : ℝ) * (CW * y * x ^ (-η)) ≤ ((I + 1 : ℕ) : ℝ) ^ d * (CW * y * x ^ (-η)) :=
          mul_le_mul_of_nonneg_right hJcard (by positivity)
      _ = CW * y * (((I + 1 : ℕ) : ℝ) ^ d * x ^ (-η)) := by ring
      _ ≤ CW * y * (1 / Real.log x ^ 2) := mul_le_mul_of_nonneg_left hxI (by positivity)
  have h2 : y / y₁ * ∑ J ∈ Js, t J ≤ atoms.length * Cn * y / Real.log x ^ 2 := by
    calc y / y₁ * ∑ J ∈ Js, t J ≤ y / y₁ * (atoms.length * (Cn * y₁ / Real.log x ^ 2)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = atoms.length * Cn * y / Real.log x ^ 2 := by field_simp
  calc |∑ g ∈ S, fA g - y / y₁ * ∑ g ∈ S, fB g| ≤ (Js.card : ℝ) * (CW * y * x ^ (-η)) + y / y₁ * ∑ J ∈ Js, t J :=
        hsand
    _ ≤ CW * y * (1 / Real.log x ^ 2) + atoms.length * Cn * y / Real.log x ^ 2 := add_le_add h1 h2
    _ = (CW + atoms.length * Cn) * y / Real.log x ^ 2 := by ring

end ShortSieveTerm

#print axioms ShortSieveTerm.nextG_grid_le
#print axioms ShortSieveTerm.pin
#print axioms ShortSieveTerm.card_near_le
#print axioms ShortSieveTerm.typeII_uniform
#print axioms ShortSieveTerm.abs_card_cut_sub_le
