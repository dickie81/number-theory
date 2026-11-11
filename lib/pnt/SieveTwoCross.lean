/-
# Conditions between the two variables of a bilinear estimate

Plain statements. A bilinear estimate bounds `Σ_χ |Σ_i f_i F_i(χ)|·|Σ_j g_j G_j(χ)|·W(χ)` by
`C(Σ|f_i|²)^{1/2}(Σ|g_j|²)^{1/2}` for all coefficients `f` on `S₁` and `g` on `S₂`. A condition that ties `i` to `j`,
such as `u(i) ≤ v(j)`, does not factor into a coefficient of each. This file shows that such conditions cost a
factor that is logarithmic in the number of values.

* `BilBd Ξs W F G S₁ S₂ C X`: the kernel `X` keeps the bound `C`: for all `f` and `g`,
  `Σ_χ |Σ_{i∈S₁} Σ_{j∈S₂} f_i g_j X_{ij} F_i(χ) G_j(χ)|·W(χ) ≤ C(Σ|f_i|²)^{1/2}(Σ|g_j|²)^{1/2}`.
* `BilBd.cmp_nat`: for `W ≥ 0` and `C ≥ 0`, if `X` keeps `C` and `u`, `v` take values below `2^N`, then
  `X_{ij}·1[u(i) ≤ v(j)]` keeps `(N + 1)C`.
* `BilBd.cmp_le`, `BilBd.cmp_lt`: the same for real `u` and `v` and the conditions `u(i) ≤ v(j)` and `u(i) < v(j)`,
  with `|S₂| < 2^N`.
* `Cross`, `kern`, `BilBd.cmp_list`: a list of `k` such conditions, strict or not, costs `(N + 1)^k`; `kern_eq`
  writes the product of their indicators as the indicator of their conjunction.

The proof of `cmp_nat` is by induction on `N`. With `d = 2^N` and `u, v < 2d`, write `f = f₀ + f₁` and `g = g₀ + g₁`
by whether `u < d` and `v < d`. Then `1[u ≤ v] = 1[u < d ≤ v] + (1[u, v < d] + 1[u, v ≥ d])·1[u mod d ≤ v mod d]`,
so the sum splits into one with the kernel `X` and the coefficients `f₀`, `g₁`, and two with the kernel
`X·1[u mod d ≤ v mod d]` and the coefficients `f₀`, `g₀` and `f₁`, `g₁`. The first is at most `C|f₀||g₁| ≤ C|f||g|`,
and the other two at most `(N + 1)C(|f₀||g₀| + |f₁||g₁|) ≤ (N + 1)C|f||g|` by the Cauchy–Schwarz inequality,
since `|f₀|² + |f₁|² = |f|²`. For real values, `u` and `v` are replaced by their ranks among the values of `v` on
`S₂`: `u(i) ≤ v(j)` iff `#{w < u(i)} ≤ #{w < v(j)}`, and `u(i) < v(j)` iff `#{w ≤ u(i)} ≤ #{w < v(j)}`, `w` over
those values.

The file imports only Mathlib.
-/
import Mathlib

open Finset

namespace SieveTwoCross

variable {Ξ ι₁ ι₂ : Type*}

/-- The kernel `X` keeps the bilinear bound `C`: for all coefficients `f` and `g`,
`Σ_χ |Σ_{i∈S₁} Σ_{j∈S₂} f_i g_j X_{ij} F_i(χ) G_j(χ)|·W(χ) ≤ C(Σ|f_i|²)^{1/2}(Σ|g_j|²)^{1/2}`. -/
def BilBd (Ξs : Finset Ξ) (W : Ξ → ℝ) (F : Ξ → ι₁ → ℂ) (G : Ξ → ι₂ → ℂ) (S₁ : Finset ι₁) (S₂ : Finset ι₂)
    (C : ℝ) (X : ι₁ → ι₂ → ℂ) : Prop :=
  ∀ (f : ι₁ → ℂ) (g : ι₂ → ℂ),
    ∑ χ ∈ Ξs, ‖∑ i ∈ S₁, ∑ j ∈ S₂, f i * g j * X i j * (F χ i * G χ j)‖ * W χ ≤
      C * (Real.sqrt (∑ i ∈ S₁, ‖f i‖ ^ 2) * Real.sqrt (∑ j ∈ S₂, ‖g j‖ ^ 2))

variable {Ξs : Finset Ξ} {W : Ξ → ℝ} {F : Ξ → ι₁ → ℂ} {G : Ξ → ι₂ → ℂ} {S₁ : Finset ι₁} {S₂ : Finset ι₂}

/-- Two kernels that agree on `S₁ × S₂` keep the same bounds. -/
theorem BilBd.congr {C : ℝ} {X X' : ι₁ → ι₂ → ℂ} (h : BilBd Ξs W F G S₁ S₂ C X)
    (hX : ∀ i ∈ S₁, ∀ j ∈ S₂, X i j = X' i j) : BilBd Ξs W F G S₁ S₂ C X' := by
  intro f g
  have heq : ∀ χ, ∑ i ∈ S₁, ∑ j ∈ S₂, f i * g j * X' i j * (F χ i * G χ j) =
      ∑ i ∈ S₁, ∑ j ∈ S₂, f i * g j * X i j * (F χ i * G χ j) := fun χ =>
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [hX i hi j hj]
  simp only [heq]
  exact h f g

/-- A larger constant is kept. -/
theorem BilBd.mono {C C' : ℝ} {X : ι₁ → ι₂ → ℂ} (h : BilBd Ξs W F G S₁ S₂ C X) (hC : C ≤ C') :
    BilBd Ξs W F G S₁ S₂ C' X := fun f g =>
  (h f g).trans (mul_le_mul_of_nonneg_right hC (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- The squares of the norms of the two parts of `f`, where a condition holds and where it fails, add up. -/
theorem sqrt_split {ι : Type*} (S : Finset ι) (f : ι → ℂ) (p : ι → Prop) [DecidablePred p] :
    Real.sqrt (∑ i ∈ S, ‖if p i then f i else 0‖ ^ 2) ^ 2 +
        Real.sqrt (∑ i ∈ S, ‖if p i then 0 else f i‖ ^ 2) ^ 2 =
      Real.sqrt (∑ i ∈ S, ‖f i‖ ^ 2) ^ 2 := by
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p i <;> simp [h]

/-- A part of `f` has at most the norm of `f`. -/
theorem sqrt_part_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) (p : ι → Prop) [DecidablePred p] :
    Real.sqrt (∑ i ∈ S, ‖if p i then f i else 0‖ ^ 2) ≤ Real.sqrt (∑ i ∈ S, ‖f i‖ ^ 2) := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : p i <;> simp [h]

/-- The Cauchy–Schwarz inequality for two terms. -/
theorem two_cs {a₀ a₁ b₀ b₁ A B : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hAe : a₀ ^ 2 + a₁ ^ 2 = A ^ 2) (hBe : b₀ ^ 2 + b₁ ^ 2 = B ^ 2) :
    a₀ * b₀ + a₁ * b₁ ≤ A * B := by
  have h : (a₀ * b₀ + a₁ * b₁) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow, ← hAe, ← hBe]
    nlinarith [sq_nonneg (a₀ * b₁ - a₁ * b₀)]
  have h1 : 0 ≤ a₀ * b₀ + a₁ * b₁ := by positivity
  have h2 : 0 ≤ A * B := mul_nonneg hA hB
  have h3 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at h3

/-- **A condition `u(i) ≤ v(j)` with values below `2^N` costs a factor `N + 1`.** For `W ≥ 0` and `C ≥ 0`: if the
kernel `X` keeps the bound `C`, and `u < 2^N` on `S₁` and `v < 2^N` on `S₂`, then `X_{ij}·1[u(i) ≤ v(j)]` keeps
`(N + 1)C`. -/
theorem BilBd.cmp_nat (hW : ∀ χ ∈ Ξs, 0 ≤ W χ) {C : ℝ} (hC : 0 ≤ C) {X : ι₁ → ι₂ → ℂ}
    (hX : BilBd Ξs W F G S₁ S₂ C X) (N : ℕ) :
    ∀ (u : ι₁ → ℕ) (v : ι₂ → ℕ), (∀ i ∈ S₁, u i < 2 ^ N) → (∀ j ∈ S₂, v j < 2 ^ N) →
      BilBd Ξs W F G S₁ S₂ ((N + 1 : ℕ) * C) (fun i j => X i j * if u i ≤ v j then 1 else 0) := by
  induction N with
  | zero =>
    intro u v hu hv
    have h1 : BilBd Ξs W F G S₁ S₂ C (fun i j => X i j * if u i ≤ v j then 1 else 0) :=
      hX.congr fun i hi j hj => by
        have h1 := hu i hi
        have h2 := hv j hj
        simp only [pow_zero, Nat.lt_one_iff] at h1 h2
        simp [h1, h2]
    simpa using h1
  | succ N ih =>
    intro u v hu hv f g
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = 2 ^ N := ⟨_, rfl⟩
    have hd0 : 0 < d := by rw [hd]; positivity
    have hmod : ∀ i ∈ S₁, u i % d < 2 ^ N := fun i _ => hd ▸ Nat.mod_lt _ hd0
    have hmod' : ∀ j ∈ S₂, v j % d < 2 ^ N := fun j _ => hd ▸ Nat.mod_lt _ hd0
    have hT₁ := hX (fun i => if u i < d then f i else 0) (fun j => if v j < d then 0 else g j)
    have hT₂ := ih (fun i => u i % d) (fun j => v j % d) hmod hmod'
      (fun i => if u i < d then f i else 0) (fun j => if v j < d then g j else 0)
    have hT₃ := ih (fun i => u i % d) (fun j => v j % d) hmod hmod'
      (fun i => if u i < d then 0 else f i) (fun j => if v j < d then 0 else g j)
    -- the kernel splits
    have hsplit : ∀ χ,
        ∑ i ∈ S₁, ∑ j ∈ S₂, f i * g j * (X i j * if u i ≤ v j then 1 else 0) * (F χ i * G χ j) =
          ∑ i ∈ S₁, ∑ j ∈ S₂, (if u i < d then f i else 0) * (if v j < d then 0 else g j) * X i j *
              (F χ i * G χ j) +
            ∑ i ∈ S₁, ∑ j ∈ S₂, (if u i < d then f i else 0) * (if v j < d then g j else 0) *
              (X i j * if u i % d ≤ v j % d then 1 else 0) * (F χ i * G χ j) +
            ∑ i ∈ S₁, ∑ j ∈ S₂, (if u i < d then 0 else f i) * (if v j < d then 0 else g j) *
              (X i j * if u i % d ≤ v j % d then 1 else 0) * (F χ i * G χ j) := by
      intro χ
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hui : u i < 2 * d := by have := hu i hi; rw [pow_succ, ← hd] at this; omega
      have hvj : v j < 2 * d := by have := hv j hj; rw [pow_succ, ← hd] at this; omega
      by_cases h1 : u i < d <;> by_cases h2 : v j < d
      · have e1 : u i % d = u i := Nat.mod_eq_of_lt h1
        have e2 : v j % d = v j := Nat.mod_eq_of_lt h2
        simp [h1, h2, e1, e2]
      · have h3 : u i ≤ v j := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ u i ≤ v j := by omega
        simp [h1, h2, h3]
      · have e1 : u i % d = u i - d := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have e2 : v j % d = v j - d := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have h3 : (u i - d ≤ v j - d) ↔ u i ≤ v j := by omega
        simp [h1, h2, e1, e2, h3]
    -- the norms of the parts
    have hA := sqrt_split S₁ f (fun i => u i < d)
    have hB := sqrt_split S₂ g (fun j => v j < d)
    have hA₀ := sqrt_part_le S₁ f (fun i => u i < d)
    have hB₁ : Real.sqrt (∑ j ∈ S₂, ‖if v j < d then 0 else g j‖ ^ 2) ≤ Real.sqrt (∑ j ∈ S₂, ‖g j‖ ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
      by_cases h : v j < d <;> simp [h]
    obtain ⟨a₀, ha₀⟩ : ∃ a : ℝ, a = Real.sqrt (∑ i ∈ S₁, ‖if u i < d then f i else 0‖ ^ 2) := ⟨_, rfl⟩
    obtain ⟨a₁, ha₁⟩ : ∃ a : ℝ, a = Real.sqrt (∑ i ∈ S₁, ‖if u i < d then 0 else f i‖ ^ 2) := ⟨_, rfl⟩
    obtain ⟨b₀, hb₀⟩ : ∃ a : ℝ, a = Real.sqrt (∑ j ∈ S₂, ‖if v j < d then g j else 0‖ ^ 2) := ⟨_, rfl⟩
    obtain ⟨b₁, hb₁⟩ : ∃ a : ℝ, a = Real.sqrt (∑ j ∈ S₂, ‖if v j < d then 0 else g j‖ ^ 2) := ⟨_, rfl⟩
    obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = Real.sqrt (∑ i ∈ S₁, ‖f i‖ ^ 2) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ a : ℝ, a = Real.sqrt (∑ j ∈ S₂, ‖g j‖ ^ 2) := ⟨_, rfl⟩
    rw [← ha₀, ← ha₁, ← hAdef] at hA
    rw [← hb₀, ← hb₁, ← hBdef] at hB
    rw [← ha₀, ← hAdef] at hA₀
    rw [← hb₁, ← hBdef] at hB₁
    rw [← ha₀, ← hb₁] at hT₁
    rw [← ha₀, ← hb₀] at hT₂
    rw [← ha₁, ← hb₁] at hT₃
    rw [← hAdef, ← hBdef]
    have ha₀n : 0 ≤ a₀ := ha₀ ▸ Real.sqrt_nonneg _
    have ha₁n : 0 ≤ a₁ := ha₁ ▸ Real.sqrt_nonneg _
    have hb₀n : 0 ≤ b₀ := hb₀ ▸ Real.sqrt_nonneg _
    have hb₁n : 0 ≤ b₁ := hb₁ ▸ Real.sqrt_nonneg _
    have hAn : 0 ≤ A := hAdef ▸ Real.sqrt_nonneg _
    have hBn : 0 ≤ B := hBdef ▸ Real.sqrt_nonneg _
    have h1 : a₀ * b₁ ≤ A * B := mul_le_mul hA₀ hB₁ hb₁n hAn
    have h2 : a₀ * b₀ + a₁ * b₁ ≤ A * B := two_cs ha₀n ha₁n hb₀n hb₁n hAn hBn hA hB
    have e1 : C * (a₀ * b₁) ≤ C * (A * B) := mul_le_mul_of_nonneg_left h1 hC
    have e2 : ((N + 1 : ℕ) : ℝ) * C * (a₀ * b₀ + a₁ * b₁) ≤ ((N + 1 : ℕ) : ℝ) * C * (A * B) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg _) hC)
    calc ∑ χ ∈ Ξs, ‖∑ i ∈ S₁, ∑ j ∈ S₂, f i * g j * (X i j * if u i ≤ v j then 1 else 0) *
            (F χ i * G χ j)‖ * W χ
        ≤ ∑ χ ∈ Ξs,
            (‖∑ i ∈ S₁, ∑ j ∈ S₂, (if u i < d then f i else 0) * (if v j < d then 0 else g j) * X i j *
                (F χ i * G χ j)‖ * W χ +
              ‖∑ i ∈ S₁, ∑ j ∈ S₂, (if u i < d then f i else 0) * (if v j < d then g j else 0) *
                (X i j * if u i % d ≤ v j % d then 1 else 0) * (F χ i * G χ j)‖ * W χ +
              ‖∑ i ∈ S₁, ∑ j ∈ S₂, (if u i < d then 0 else f i) * (if v j < d then 0 else g j) *
                (X i j * if u i % d ≤ v j % d then 1 else 0) * (F χ i * G χ j)‖ * W χ) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          rw [hsplit χ, ← add_mul, ← add_mul]
          exact mul_le_mul_of_nonneg_right (norm_add₃_le) (hW χ hχ)
      _ ≤ C * (a₀ * b₁) + ((N + 1 : ℕ) : ℝ) * C * (a₀ * b₀) + ((N + 1 : ℕ) : ℝ) * C * (a₁ * b₁) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          exact add_le_add (add_le_add hT₁ hT₂) hT₃
      _ ≤ ((N + 1 + 1 : ℕ) : ℝ) * C * (A * B) := by
          push_cast at e2 ⊢
          linarith

/-- **A condition `u(i) ≤ v(j)` with real values costs a factor `N + 1`**, for `|S₂| < 2^N`. -/
theorem BilBd.cmp_le (hW : ∀ χ ∈ Ξs, 0 ≤ W χ) {C : ℝ} (hC : 0 ≤ C) {X : ι₁ → ι₂ → ℂ}
    (hX : BilBd Ξs W F G S₁ S₂ C X) {N : ℕ} (hN : S₂.card < 2 ^ N) (u : ι₁ → ℝ) (v : ι₂ → ℝ) :
    BilBd Ξs W F G S₁ S₂ ((N + 1 : ℕ) * C) (fun i j => X i j * if u i ≤ v j then 1 else 0) := by
  classical
  have hcard : ∀ p : ℝ → Prop, ∀ [DecidablePred p], ((S₂.image v).filter p).card < 2 ^ N := fun p _ =>
    lt_of_le_of_lt ((Finset.card_filter_le _ _).trans Finset.card_image_le) hN
  refine (hX.cmp_nat hW hC N (fun i => ((S₂.image v).filter (fun w => w < u i)).card)
    (fun j => ((S₂.image v).filter (fun w => w < v j)).card) (fun i _ => hcard _) (fun j _ => hcard _)).congr ?_
  intro i _ j hj
  have hiff : ((S₂.image v).filter (fun w => w < u i)).card ≤ ((S₂.image v).filter (fun w => w < v j)).card ↔
      u i ≤ v j := by
    constructor
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      have hsub : insert (v j) ((S₂.image v).filter (fun w => w < v j)) ⊆
          (S₂.image v).filter (fun w => w < u i) := by
        intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem v hj, hlt⟩
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
          exact Finset.mem_filter.2 ⟨h1, h2.trans hlt⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp)] at hc
      omega
    · intro h
      refine Finset.card_le_card fun w hw => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨h1, lt_of_lt_of_le h2 h⟩
  simp only [hiff]

/-- **A condition `u(i) < v(j)` with real values costs a factor `N + 1`**, for `|S₂| < 2^N`. -/
theorem BilBd.cmp_lt (hW : ∀ χ ∈ Ξs, 0 ≤ W χ) {C : ℝ} (hC : 0 ≤ C) {X : ι₁ → ι₂ → ℂ}
    (hX : BilBd Ξs W F G S₁ S₂ C X) {N : ℕ} (hN : S₂.card < 2 ^ N) (u : ι₁ → ℝ) (v : ι₂ → ℝ) :
    BilBd Ξs W F G S₁ S₂ ((N + 1 : ℕ) * C) (fun i j => X i j * if u i < v j then 1 else 0) := by
  classical
  have hcard : ∀ p : ℝ → Prop, ∀ [DecidablePred p], ((S₂.image v).filter p).card < 2 ^ N := fun p _ =>
    lt_of_le_of_lt ((Finset.card_filter_le _ _).trans Finset.card_image_le) hN
  refine (hX.cmp_nat hW hC N (fun i => ((S₂.image v).filter (fun w => w ≤ u i)).card)
    (fun j => ((S₂.image v).filter (fun w => w < v j)).card) (fun i _ => hcard _) (fun j _ => hcard _)).congr ?_
  intro i _ j hj
  have hiff : ((S₂.image v).filter (fun w => w ≤ u i)).card ≤ ((S₂.image v).filter (fun w => w < v j)).card ↔
      u i < v j := by
    constructor
    · intro h
      by_contra hle
      rw [not_lt] at hle
      have hsub : insert (v j) ((S₂.image v).filter (fun w => w < v j)) ⊆
          (S₂.image v).filter (fun w => w ≤ u i) := by
        intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem v hj, hle⟩
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
          exact Finset.mem_filter.2 ⟨h1, h2.le.trans hle⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp)] at hc
      omega
    · intro h
      refine Finset.card_le_card fun w hw => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨h1, lt_of_le_of_lt h2 h⟩
  simp only [hiff]

/-- A condition between `i` and `j`: `u(i) < v(j)` if strict, `u(i) ≤ v(j)` otherwise. -/
structure Cross (ι₁ ι₂ : Type*) where
  u : ι₁ → ℝ
  v : ι₂ → ℝ
  strict : Bool

/-- The condition holds at `(i, j)`. -/
def Cross.holds (c : Cross ι₁ ι₂) (i : ι₁) (j : ι₂) : Prop :=
  if c.strict then c.u i < c.v j else c.u i ≤ c.v j

open Classical in
/-- The product of the indicators of a list of conditions. -/
noncomputable def kern (l : List (Cross ι₁ ι₂)) (i : ι₁) (j : ι₂) : ℂ :=
  (l.map fun c => if c.holds i j then (1 : ℂ) else 0).prod

open Classical in
/-- The product of the indicators is the indicator of the conjunction. -/
theorem kern_eq (l : List (Cross ι₁ ι₂)) (i : ι₁) (j : ι₂) :
    kern l i j = if ∀ c ∈ l, c.holds i j then 1 else 0 := by
  induction l with
  | nil => simp [kern]
  | cons c l ih =>
    unfold kern at ih ⊢
    rw [List.map_cons, List.prod_cons, ih]
    by_cases h1 : c.holds i j <;> by_cases h2 : ∀ c ∈ l, c.holds i j <;> simp [h1, h2]

open Classical in
/-- **A list of `k` conditions between `i` and `j` costs a factor `(N + 1)^k`**, for `W ≥ 0`, `C ≥ 0` and
`|S₂| < 2^N`. -/
theorem BilBd.cmp_list (hW : ∀ χ ∈ Ξs, 0 ≤ W χ) {C : ℝ} (hC : 0 ≤ C) {X : ι₁ → ι₂ → ℂ}
    (hX : BilBd Ξs W F G S₁ S₂ C X) {N : ℕ} (hN : S₂.card < 2 ^ N) (l : List (Cross ι₁ ι₂)) :
    BilBd Ξs W F G S₁ S₂ (((N + 1 : ℕ) : ℝ) ^ l.length * C) (fun i j => X i j * kern l i j) := by
  induction l with
  | nil =>
    refine (hX.congr fun i _ j _ => ?_).mono (by simp)
    simp [kern]
  | cons c l ih =>
    have hC' : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ l.length * C := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC
    have hstep : BilBd Ξs W F G S₁ S₂ (((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ l.length * C))
        (fun i j => X i j * kern l i j * if c.holds i j then 1 else 0) := by
      by_cases hs : c.strict
      · refine (ih.cmp_lt hW hC' hN c.u c.v).congr fun i _ j _ => ?_
        simp [Cross.holds, hs]
      · refine (ih.cmp_le hW hC' hN c.u c.v).congr fun i _ j _ => ?_
        simp [Cross.holds, hs]
    refine (hstep.congr fun i _ j _ => ?_).mono (le_of_eq ?_)
    · unfold kern
      rw [List.map_cons, List.prod_cons]
      ring
    · rw [List.length_cons, pow_succ]
      ring

end SieveTwoCross

#print axioms SieveTwoCross.BilBd.cmp_list
#print axioms SieveTwoCross.kern_eq
