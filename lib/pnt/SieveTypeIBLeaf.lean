/-
# The leaves of a tree by the bilinear Type I estimate: the sandwich

Plain statements. For a unit `a` mod `q` and `N₁ ≤ N₂`: `gA n = 1[n ≡ a]`, `gU n = 1[(n, q) = 1]`, and
`rng d k = 1[N₁ < dk ≤ N₂]`. A sifted count is sandwiched by sieve weights: `R` (the sifted indicator, `0 ≤ R ≤ 1`)
lies between `Σ_{τ∈S⁻} λ⁻_τ 1[f⁻_τ ∣ m]` and `Σ_{σ∈S⁺} λ⁺_σ 1[f⁺_σ ∣ m]`. Over each pair of blocks of the values
`d₁ = π₁(y₁)f` and `d₂ = π₂(y₂)`, splines `wm ≤ rng(d₁d₂, ·) ≤ wp` (`sp`) replace the range of the cofactor.

* `sum_mul_dvd`: for `f ≥ 1`, `Σ_{m≤N} 1[f ∣ m]F(m) = Σ_{k≤N} F(fk)` when `F` vanishes above `N`.
* `brun_upper`, `brun_lower`: the sifted sums of `g ≥ 0` over the range, against the weights' sums.
* `spline_upper`, `spline_lower`: the sign-split sandwich: for `λ = λ₊ − λ₋` (the positive and negative parts),
  `λ Σ_k rng(d, k)g(dk) ≤ λ₊ Σ_k wp(k)g(dk) − λ₋ Σ_k wm(k)g(dk)`, and the reverse with `wp`, `wm` exchanged.

The file imports `SieveTypeIBFam.lean`.
-/
import SieveTypeIBFam

open Finset

namespace SieveTypeIBLeaf

open SieveTypeIB SieveSpline SieveTypeIBFam

/-! ### Indicators -/

/-- `1[n ≡ a]`. -/
noncomputable def gA (q : ℕ) (a : ZMod q) (n : ℕ) : ℝ := if (n : ZMod q) = a then 1 else 0

open Classical in
/-- `1[(n, q) = 1]`. -/
noncomputable def gU (q : ℕ) (n : ℕ) : ℝ := if IsUnit (n : ZMod q) then 1 else 0

/-- `1[N₁ < dk ≤ N₂]`. -/
noncomputable def rng (N₁ N₂ d k : ℕ) : ℝ := if N₁ < d * k ∧ d * k ≤ N₂ then 1 else 0

/-- `1[f ∣ m]`. -/
noncomputable def dv (f m : ℕ) : ℝ := if f ∣ m then 1 else 0

theorem gA_nonneg (q : ℕ) (a : ZMod q) (n : ℕ) : 0 ≤ gA q a n := by unfold gA; split_ifs <;> norm_num
theorem gU_nonneg (q n : ℕ) : 0 ≤ gU q n := by unfold gU; split_ifs <;> norm_num
theorem gU_le_one (q n : ℕ) : gU q n ≤ 1 := by unfold gU; split_ifs <;> norm_num
theorem rng_nonneg (N₁ N₂ d k : ℕ) : 0 ≤ rng N₁ N₂ d k := by unfold rng; split_ifs <;> norm_num

/-- `dw = gA − gU/φ(q)`. -/
theorem dw_eq (q : ℕ) (a : ZMod q) (n : ℕ) :
    SieveFamily.dw q a n = ((gA q a n - gU q n / q.totient : ℝ) : ℂ) := by
  rw [SieveFamily.dw, gA, gU]
  push_cast
  split_ifs <;> simp

/-- `rng` vanishes above `N₂`: `rng(d, k) = 0` for `d ≥ 1` and `k > N₂`. -/
theorem rng_eq_zero {N₁ N₂ d k : ℕ} (hd : 1 ≤ d) (hk : N₂ < k) : rng N₁ N₂ d k = 0 := by
  rw [rng, ite_eq_right]
  intro h
  have : k ≤ d * k := Nat.le_mul_of_pos_left k hd
  omega

/-! ### Multiples -/

/-- `Σ_{m≤N} 1[f ∣ m]F(m) = Σ_{k≤N} F(fk)` for `f ≥ 1`, when `F` vanishes above `N`. -/
theorem sum_mul_dvd (N f : ℕ) (hf : 1 ≤ f) (F : ℕ → ℝ) (hF : ∀ m, N < m → F m = 0) :
    ∑ m ∈ range (N + 1), dv f m * F m = ∑ k ∈ range (N + 1), F (f * k) := by
  have h1 : ∑ m ∈ range (N + 1), dv f m * F m = ∑ m ∈ (range (N + 1)).filter (f ∣ ·), F m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold dv; split_ifs <;> simp
  have h2 : ∑ k ∈ range (N + 1), F (f * k) = ∑ k ∈ (range (N + 1)).filter (fun k => f * k ≤ N), F (f * k) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · exact hF _ (by omega)
  rw [h1, h2]
  refine Finset.sum_bij' (fun m _ => m / f) (fun k _ => f * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
    obtain ⟨hmN, c, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left c (by omega)]
    have : c ≤ f * c := Nat.le_mul_of_pos_left c (by omega)
    exact ⟨by omega, by omega⟩
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, dvd_mul_right f k⟩
  · intro m hm
    rw [Finset.mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro k _
    exact Nat.mul_div_cancel_left k (by omega)
  · intro m hm
    rw [Finset.mem_filter] at hm
    rw [Nat.mul_div_cancel' hm.2]

/-! ### The sieve's sandwich -/

/-- **Brun, above**: for `d ≥ 1`, `g ≥ 0` and `R ≤ Σ_σ λ_σ1[f_σ ∣ ·]` with `f_σ ≥ 1`,
`Σ_{m≤N₂} rng(d, m)R(m)g(dm) ≤ Σ_σ λ_σ Σ_{k≤N₂} rng(df_σ, k)g(df_σk)`. -/
theorem brun_upper (N₁ N₂ d : ℕ) (hd : 1 ≤ d) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (R : ℕ → ℝ) {κ : Type*}
    (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (hf : ∀ σ ∈ S, 1 ≤ f σ)
    (hR : ∀ m, R m ≤ ∑ σ ∈ S, lam σ * dv (f σ) m) :
    ∑ m ∈ range (N₂ + 1), rng N₁ N₂ d m * R m * g (d * m) ≤
      ∑ σ ∈ S, lam σ * ∑ k ∈ range (N₂ + 1), rng N₁ N₂ (d * f σ) k * g (d * f σ * k) := by
  calc ∑ m ∈ range (N₂ + 1), rng N₁ N₂ d m * R m * g (d * m)
      ≤ ∑ m ∈ range (N₂ + 1), rng N₁ N₂ d m * (∑ σ ∈ S, lam σ * dv (f σ) m) * g (d * m) :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hR m) (rng_nonneg _ _ _ _)) (hg _)
    _ = ∑ σ ∈ S, lam σ * ∑ m ∈ range (N₂ + 1), dv (f σ) m * (rng N₁ N₂ d m * g (d * m)) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ σ ∈ S, lam σ * ∑ k ∈ range (N₂ + 1), rng N₁ N₂ (d * f σ) k * g (d * f σ * k) := by
        refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [sum_mul_dvd N₂ (f σ) (hf σ hσ) _ fun m hm => by rw [rng_eq_zero hd hm, zero_mul]]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [rng, rng, show d * (f σ * k) = d * f σ * k by ring]

/-- **Brun, below**: for `d ≥ 1`, `g ≥ 0` and `Σ_τ λ_τ1[f_τ ∣ ·] ≤ R` with `f_τ ≥ 1`,
`Σ_τ λ_τ Σ_{k≤N₂} rng(df_τ, k)g(df_τk) ≤ Σ_{m≤N₂} rng(d, m)R(m)g(dm)`. -/
theorem brun_lower (N₁ N₂ d : ℕ) (hd : 1 ≤ d) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (R : ℕ → ℝ) {κ : Type*}
    (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (hf : ∀ τ ∈ S, 1 ≤ f τ)
    (hR : ∀ m, ∑ τ ∈ S, lam τ * dv (f τ) m ≤ R m) :
    ∑ τ ∈ S, lam τ * ∑ k ∈ range (N₂ + 1), rng N₁ N₂ (d * f τ) k * g (d * f τ * k) ≤
      ∑ m ∈ range (N₂ + 1), rng N₁ N₂ d m * R m * g (d * m) := by
  calc ∑ τ ∈ S, lam τ * ∑ k ∈ range (N₂ + 1), rng N₁ N₂ (d * f τ) k * g (d * f τ * k)
      = ∑ τ ∈ S, lam τ * ∑ m ∈ range (N₂ + 1), dv (f τ) m * (rng N₁ N₂ d m * g (d * m)) := by
        refine Finset.sum_congr rfl fun τ hτ => ?_
        rw [sum_mul_dvd N₂ (f τ) (hf τ hτ) _ fun m hm => by rw [rng_eq_zero hd hm, zero_mul]]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [rng, rng, show d * (f τ * k) = d * f τ * k by ring]
    _ = ∑ m ∈ range (N₂ + 1), rng N₁ N₂ d m * (∑ τ ∈ S, lam τ * dv (f τ) m) * g (d * m) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun m _ => by ring
    _ ≤ ∑ m ∈ range (N₂ + 1), rng N₁ N₂ d m * R m * g (d * m) :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hR m) (rng_nonneg _ _ _ _)) (hg _)

/-- The positive part `λ₊ = max(λ, 0)`. -/
noncomputable def ppart (x : ℝ) : ℝ := max x 0

/-- The negative part `λ₋ = max(−λ, 0)`. -/
noncomputable def npart (x : ℝ) : ℝ := max (-x) 0

theorem ppart_sub_npart (x : ℝ) : ppart x - npart x = x := by
  unfold ppart npart
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem ppart_nonneg (x : ℝ) : 0 ≤ ppart x := le_max_right _ _
theorem npart_nonneg (x : ℝ) : 0 ≤ npart x := le_max_right _ _

theorem ppart_add_npart (x : ℝ) : ppart x + npart x = |x| := by
  unfold ppart npart
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring

/-- **The sign-split sandwich, above**: for `wm ≤ rng ≤ wp` and `g ≥ 0` on a finite set `K`,
`λΣ_K rng·g ≤ λ₊Σ_K wpg − λ₋Σ_K wmg`. -/
theorem split_upper {K : Finset ℕ} (lam : ℝ) (r wp wm g : ℕ → ℝ) (hg : ∀ k ∈ K, 0 ≤ g k)
    (hup : ∀ k ∈ K, r k ≤ wp k) (hlo : ∀ k ∈ K, wm k ≤ r k) :
    lam * ∑ k ∈ K, r k * g k ≤ ppart lam * ∑ k ∈ K, wp k * g k - npart lam * ∑ k ∈ K, wm k * g k := by
  have h1 : ∑ k ∈ K, r k * g k ≤ ∑ k ∈ K, wp k * g k :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hup k hk) (hg k hk)
  have h2 : ∑ k ∈ K, wm k * g k ≤ ∑ k ∈ K, r k * g k :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hlo k hk) (hg k hk)
  have e := ppart_sub_npart lam
  have hp := ppart_nonneg lam
  have hn := npart_nonneg lam
  calc lam * ∑ k ∈ K, r k * g k = ppart lam * ∑ k ∈ K, r k * g k - npart lam * ∑ k ∈ K, r k * g k := by
        rw [← sub_mul, e]
    _ ≤ ppart lam * ∑ k ∈ K, wp k * g k - npart lam * ∑ k ∈ K, wm k * g k := by
        have := mul_le_mul_of_nonneg_left h1 hp
        have := mul_le_mul_of_nonneg_left h2 hn
        linarith

/-- **The sign-split sandwich, below**: `λ₊Σ_K wmg − λ₋Σ_K wpg ≤ λΣ_K rng·g`. -/
theorem split_lower {K : Finset ℕ} (lam : ℝ) (r wp wm g : ℕ → ℝ) (hg : ∀ k ∈ K, 0 ≤ g k)
    (hup : ∀ k ∈ K, r k ≤ wp k) (hlo : ∀ k ∈ K, wm k ≤ r k) :
    ppart lam * ∑ k ∈ K, wm k * g k - npart lam * ∑ k ∈ K, wp k * g k ≤ lam * ∑ k ∈ K, r k * g k := by
  have h1 : ∑ k ∈ K, r k * g k ≤ ∑ k ∈ K, wp k * g k :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hup k hk) (hg k hk)
  have h2 : ∑ k ∈ K, wm k * g k ≤ ∑ k ∈ K, r k * g k :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hlo k hk) (hg k hk)
  have e := ppart_sub_npart lam
  have hp := ppart_nonneg lam
  have hn := npart_nonneg lam
  calc ppart lam * ∑ k ∈ K, wm k * g k - npart lam * ∑ k ∈ K, wp k * g k
      ≤ ppart lam * ∑ k ∈ K, r k * g k - npart lam * ∑ k ∈ K, r k * g k := by
        have := mul_le_mul_of_nonneg_left h1 hn
        have := mul_le_mul_of_nonneg_left h2 hp
        linarith
    _ = lam * ∑ k ∈ K, r k * g k := by rw [← sub_mul, e]

/-- A spline's sum over a set containing its support is its sum over the support. -/
theorem sum_spl_superset {K : Finset ℕ} (A B ℓ r : ℕ) (hK : supp A B ℓ r ⊆ K) (G : ℕ → ℝ) :
    ∑ k ∈ K, spl A B ℓ r k * G k = ∑ k ∈ supp A B ℓ r, spl A B ℓ r k * G k := by
  refine (Finset.sum_subset hK fun k _ hk => ?_).symm
  rw [spl_eq_zero A B ℓ r k hk, zero_mul]

/-- `rng(d, ·)`'s sum over a set containing `[0, N₂]` is its sum over `[0, N₂]`, for `d ≥ 1`. -/
theorem sum_rng_superset {K : Finset ℕ} (N₁ N₂ d : ℕ) (hd : 1 ≤ d) (hK : range (N₂ + 1) ⊆ K) (G : ℕ → ℝ) :
    ∑ k ∈ K, rng N₁ N₂ d k * G k = ∑ k ∈ range (N₂ + 1), rng N₁ N₂ d k * G k := by
  refine (Finset.sum_subset hK fun k _ hk => ?_).symm
  rw [Finset.mem_range, not_lt] at hk
  rw [rng_eq_zero hd (by omega), zero_mul]

/-! ### One leaf -/

/-- A spline given by its data `(A, B, ℓ, r)`. -/
noncomputable def splv (t : ℕ × ℕ × ℕ × ℕ) (k : ℕ) : ℝ := spl t.1 t.2.1 t.2.2.1 t.2.2.2 k

/-- Its support. -/
def suppv (t : ℕ × ℕ × ℕ × ℕ) : Finset ℕ := supp t.1 t.2.1 t.2.2.1 t.2.2.2

/-- The real form of `dw`: `1[n ≡ a] − 1[(n, q) = 1]/φ(q)`. -/
noncomputable def dwR (q : ℕ) (a : ZMod q) (n : ℕ) : ℝ := gA q a n - gU q n / q.totient

/-- `Σ_{k∈supp} w(k)g(dk)`. -/
noncomputable def ssum (t : ℕ × ℕ × ℕ × ℕ) (g : ℕ → ℝ) (d : ℕ) : ℝ := ∑ k ∈ suppv t, splv t k * g (d * k)

/-- `Σ_{k≤N₂} rng(d, k)g(dk)`. -/
noncomputable def rsum (N₁ N₂ : ℕ) (g : ℕ → ℝ) (d : ℕ) : ℝ := ∑ k ∈ range (N₂ + 1), rng N₁ N₂ d k * g (d * k)

/-- **The sign-split sandwich of one term**: if `w⁻ ≤ rng(d, ·) ≤ w⁺` everywhere and `g ≥ 0`, with `d ≥ 1`, then
`λ·rsum(g) ≤ λ₊·ssum⁺(g) − λ₋·ssum⁻(g)` and `λ₊·ssum⁻(g) − λ₋·ssum⁺(g) ≤ λ·rsum(g)`. -/
theorem term_sandwich (N₁ N₂ d : ℕ) (hd : 1 ≤ d) (lam : ℝ) (tp tm : ℕ × ℕ × ℕ × ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (hup : ∀ k, rng N₁ N₂ d k ≤ splv tp k) (hlo : ∀ k, splv tm k ≤ rng N₁ N₂ d k) :
    lam * rsum N₁ N₂ g d ≤ ppart lam * ssum tp g d - npart lam * ssum tm g d ∧
      ppart lam * ssum tm g d - npart lam * ssum tp g d ≤ lam * rsum N₁ N₂ g d := by
  set K := range (N₂ + 1) ∪ suppv tp ∪ suppv tm with hK
  have hKr : range (N₂ + 1) ⊆ K := fun k hk => by rw [hK]; simp [hk]
  have hKp : suppv tp ⊆ K := fun k hk => by rw [hK]; simp [hk]
  have hKm : suppv tm ⊆ K := fun k hk => by rw [hK]; simp [hk]
  have er : rsum N₁ N₂ g d = ∑ k ∈ K, rng N₁ N₂ d k * g (d * k) :=
    (sum_rng_superset N₁ N₂ d hd hKr (fun k => g (d * k))).symm
  have ep : ssum tp g d = ∑ k ∈ K, splv tp k * g (d * k) :=
    (sum_spl_superset _ _ _ _ hKp (fun k => g (d * k))).symm
  have em : ssum tm g d = ∑ k ∈ K, splv tm k * g (d * k) :=
    (sum_spl_superset _ _ _ _ hKm (fun k => g (d * k))).symm
  rw [er, ep, em]
  exact ⟨split_upper lam (rng N₁ N₂ d) (splv tp) (splv tm) (fun k => g (d * k)) (fun k _ => hg _)
      (fun k _ => hup k) (fun k _ => hlo k),
    split_lower lam (rng N₁ N₂ d) (splv tp) (splv tm) (fun k => g (d * k)) (fun k _ => hg _)
      (fun k _ => hup k) (fun k _ => hlo k)⟩

/-- `ssum` is additive in `g`. -/
theorem ssum_sub (t : ℕ × ℕ × ℕ × ℕ) (g h : ℕ → ℝ) (d : ℕ) (c : ℝ) :
    ssum t (fun n => g n - h n / c) d = ssum t g d - ssum t h d / c := by
  unfold ssum
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **One leaf, above.** For `d₁, d₂ ≥ 1`, sieve weights above (`S⁺`) and below (`S⁻`) of `R`, and splines `tp(·)`,
`tm(·)` with `tm ≤ rng(d₁fd₂, ·) ≤ tp` for each weight's `f`: the leaf's `Σ_m rng(d₁d₂, m)R(m)dw(d₁d₂m)` is at most the
main part `φ(q)⁻¹[Σ_σ (λ₊ssum⁺(gU) − λ₋ssum⁻(gU)) − Σ_τ λ⁻_τ rsum(gU)]` plus the bilinear part
`Σ_σ (λ₊ssum⁺(dw) − λ₋ssum⁻(dw))`. -/
theorem leaf_upper (q : ℕ) (a : ZMod q) (N₁ N₂ d₁ d₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (R : ℕ → ℝ)
    {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (hR₁ : ∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (hR₂ : ∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m)
    (tp tm : κ₁ → ℕ × ℕ × ℕ × ℕ) (hup : ∀ σ ∈ S₁, ∀ k, rng N₁ N₂ (d₁ * f₁ σ * d₂) k ≤ splv (tp σ) k)
    (hlo : ∀ σ ∈ S₁, ∀ k, splv (tm σ) k ≤ rng N₁ N₂ (d₁ * f₁ σ * d₂) k) :
    ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * dwR q a (d₁ * d₂ * m) ≤
      (∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (gU q) (d₁ * f₁ σ * d₂) -
          npart (l₁ σ) * ssum (tm σ) (gU q) (d₁ * f₁ σ * d₂)) -
        ∑ τ ∈ S₂, l₂ τ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₂ τ)) / q.totient +
      ∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (dwR q a) (d₁ * f₁ σ * d₂) -
          npart (l₁ σ) * ssum (tm σ) (dwR q a) (d₁ * f₁ σ * d₂)) := by
  have hd : 1 ≤ d₁ * d₂ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  -- split `dw` into its two counts
  have hsplit : ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * dwR q a (d₁ * d₂ * m) =
      ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gA q a (d₁ * d₂ * m) -
        (∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gU q (d₁ * d₂ * m)) / q.totient := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by unfold dwR; ring
  -- Brun above on the `A`-count, below on the units' count
  have hA := brun_upper N₁ N₂ (d₁ * d₂) hd (gA q a) (gA_nonneg q a) R S₁ f₁ l₁ hf₁ hR₁
  have hU := brun_lower N₁ N₂ (d₁ * d₂) hd (gU q) (gU_nonneg q) R S₂ f₂ l₂ hf₂ hR₂
  -- the splines on the `A`-count
  have hsand : ∀ σ ∈ S₁, l₁ σ * rsum N₁ N₂ (gA q a) (d₁ * f₁ σ * d₂) ≤
      ppart (l₁ σ) * ssum (tp σ) (gA q a) (d₁ * f₁ σ * d₂) - npart (l₁ σ) * ssum (tm σ) (gA q a) (d₁ * f₁ σ * d₂) :=
    fun σ hσ => (term_sandwich N₁ N₂ (d₁ * f₁ σ * d₂) (Nat.one_le_iff_ne_zero.2 (by
      have := hf₁ σ hσ; positivity)) (l₁ σ) (tp σ) (tm σ) (gA q a) (gA_nonneg q a) (hup σ hσ) (hlo σ hσ)).1
  have hreidx : ∀ σ, rsum N₁ N₂ (gA q a) (d₁ * f₁ σ * d₂) =
      ∑ k ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂ * f₁ σ) k * gA q a (d₁ * d₂ * f₁ σ * k) := fun σ => by
    rw [rsum, show d₁ * f₁ σ * d₂ = d₁ * d₂ * f₁ σ by ring]
  have hAs : ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gA q a (d₁ * d₂ * m) ≤
      ∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (gA q a) (d₁ * f₁ σ * d₂) -
        npart (l₁ σ) * ssum (tm σ) (gA q a) (d₁ * f₁ σ * d₂)) :=
    hA.trans (Finset.sum_le_sum fun σ hσ => by rw [← hreidx σ]; exact hsand σ hσ)
  have hUs : ∑ τ ∈ S₂, l₂ τ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₂ τ) ≤
      ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gU q (d₁ * d₂ * m) := hU
  -- `gA = gU/φ + dw` on the splines
  have hgA : ∀ t d, ssum t (gA q a) d = ssum t (gU q) d / q.totient + ssum t (dwR q a) d := by
    intro t d
    have := ssum_sub t (gA q a) (gU q) d q.totient
    rw [show (fun n => gA q a n - gU q n / q.totient) = dwR q a from rfl] at this
    linarith
  rw [hsplit]
  have hrhs : ∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (gA q a) (d₁ * f₁ σ * d₂) -
        npart (l₁ σ) * ssum (tm σ) (gA q a) (d₁ * f₁ σ * d₂)) =
      (∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (gU q) (d₁ * f₁ σ * d₂) -
          npart (l₁ σ) * ssum (tm σ) (gU q) (d₁ * f₁ σ * d₂))) / q.totient +
        ∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (dwR q a) (d₁ * f₁ σ * d₂) -
          npart (l₁ σ) * ssum (tm σ) (dwR q a) (d₁ * f₁ σ * d₂)) := by
    simp only [hgA]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hrhs] at hAs
  have hdiv := div_le_div_of_nonneg_right hUs hφ
  rw [sub_div]
  linarith

/-- **One leaf, below.** The same, with the roles of the weights exchanged: the leaf's sum is at least
`φ(q)⁻¹[Σ_τ (λ₊ssum⁻(gU) − λ₋ssum⁺(gU)) − Σ_σ λ⁺_σ rsum(gU)] + Σ_τ (λ₊ssum⁻(dw) − λ₋ssum⁺(dw))`, with the splines
`tp(τ)`, `tm(τ)` of the weights below. -/
theorem leaf_lower (q : ℕ) (a : ZMod q) (N₁ N₂ d₁ d₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (R : ℕ → ℝ)
    {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (hR₁ : ∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (hR₂ : ∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m)
    (tp tm : κ₂ → ℕ × ℕ × ℕ × ℕ) (hup : ∀ τ ∈ S₂, ∀ k, rng N₁ N₂ (d₁ * f₂ τ * d₂) k ≤ splv (tp τ) k)
    (hlo : ∀ τ ∈ S₂, ∀ k, splv (tm τ) k ≤ rng N₁ N₂ (d₁ * f₂ τ * d₂) k) :
    (∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (gU q) (d₁ * f₂ τ * d₂) -
          npart (l₂ τ) * ssum (tp τ) (gU q) (d₁ * f₂ τ * d₂)) -
        ∑ σ ∈ S₁, l₁ σ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₁ σ)) / q.totient +
      ∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (dwR q a) (d₁ * f₂ τ * d₂) -
          npart (l₂ τ) * ssum (tp τ) (dwR q a) (d₁ * f₂ τ * d₂)) ≤
    ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * dwR q a (d₁ * d₂ * m) := by
  have hd : 1 ≤ d₁ * d₂ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hsplit : ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * dwR q a (d₁ * d₂ * m) =
      ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gA q a (d₁ * d₂ * m) -
        (∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gU q (d₁ * d₂ * m)) / q.totient := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by unfold dwR; ring
  have hA := brun_lower N₁ N₂ (d₁ * d₂) hd (gA q a) (gA_nonneg q a) R S₂ f₂ l₂ hf₂ hR₂
  have hU := brun_upper N₁ N₂ (d₁ * d₂) hd (gU q) (gU_nonneg q) R S₁ f₁ l₁ hf₁ hR₁
  have hsand : ∀ τ ∈ S₂, ppart (l₂ τ) * ssum (tm τ) (gA q a) (d₁ * f₂ τ * d₂) -
      npart (l₂ τ) * ssum (tp τ) (gA q a) (d₁ * f₂ τ * d₂) ≤ l₂ τ * rsum N₁ N₂ (gA q a) (d₁ * f₂ τ * d₂) :=
    fun τ hτ => (term_sandwich N₁ N₂ (d₁ * f₂ τ * d₂) (Nat.one_le_iff_ne_zero.2 (by
      have := hf₂ τ hτ; positivity)) (l₂ τ) (tp τ) (tm τ) (gA q a) (gA_nonneg q a) (hup τ hτ) (hlo τ hτ)).2
  have hreidx : ∀ τ, rsum N₁ N₂ (gA q a) (d₁ * f₂ τ * d₂) =
      ∑ k ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂ * f₂ τ) k * gA q a (d₁ * d₂ * f₂ τ * k) := fun τ => by
    rw [rsum, show d₁ * f₂ τ * d₂ = d₁ * d₂ * f₂ τ by ring]
  have hAs : ∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (gA q a) (d₁ * f₂ τ * d₂) -
        npart (l₂ τ) * ssum (tp τ) (gA q a) (d₁ * f₂ τ * d₂)) ≤
      ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gA q a (d₁ * d₂ * m) :=
    (Finset.sum_le_sum fun τ hτ => by rw [← hreidx τ] at *; exact hsand τ hτ).trans hA
  have hgA : ∀ t d, ssum t (gA q a) d = ssum t (gU q) d / q.totient + ssum t (dwR q a) d := by
    intro t d
    have := ssum_sub t (gA q a) (gU q) d q.totient
    rw [show (fun n => gA q a n - gU q n / q.totient) = dwR q a from rfl] at this
    linarith
  rw [hsplit]
  have hlhs : ∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (gA q a) (d₁ * f₂ τ * d₂) -
        npart (l₂ τ) * ssum (tp τ) (gA q a) (d₁ * f₂ τ * d₂)) =
      (∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (gU q) (d₁ * f₂ τ * d₂) -
          npart (l₂ τ) * ssum (tp τ) (gU q) (d₁ * f₂ τ * d₂))) / q.totient +
        ∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (dwR q a) (d₁ * f₂ τ * d₂) -
          npart (l₂ τ) * ssum (tp τ) (dwR q a) (d₁ * f₂ τ * d₂)) := by
    simp only [hgA]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hlhs] at hAs
  have hUs : ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * gU q (d₁ * d₂ * m) ≤
      ∑ σ ∈ S₁, l₁ σ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₁ σ) := hU
  have hdiv := div_le_div_of_nonneg_right hUs hφ
  rw [sub_div]
  linarith

/-! ### The units' counts -/

/-- `gU` of a product. -/
theorem gU_mul (q m n : ℕ) : gU q (m * n) = gU q m * gU q n := by
  unfold gU
  by_cases hm : IsUnit (m : ZMod q) <;> by_cases hn : IsUnit (n : ZMod q)
  · simp [hm, hn, hm.mul hn]
  all_goals simp [hm, hn]

/-- `gU` against `Ew`'s indicator. -/
theorem gU_cast (q k : ℕ) [NeZero q] : ((gU q k : ℝ) : ℂ) = if IsUnit (k : ZMod q) then 1 else 0 := by
  unfold gU
  split_ifs <;> simp_all

/-- The range of `rng(d, ·)`: for `d ≥ 1`, `Σ_{k≤N₂} rng(d, k)G(k) = Σ_{⌊N₁/d⌋<k≤⌊N₂/d⌋} G(k)`. -/
theorem sum_rng_eq (N₁ N₂ d : ℕ) (hd : 1 ≤ d) (G : ℕ → ℝ) :
    ∑ k ∈ range (N₂ + 1), rng N₁ N₂ d k * G k = ∑ k ∈ Ioc (N₁ / d) (N₂ / d), G k := by
  have hset : (range (N₂ + 1)).filter (fun k => N₁ < d * k ∧ d * k ≤ N₂) = Ioc (N₁ / d) (N₂ / d) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.div_lt_iff_lt_mul (by omega),
      Nat.le_div_iff_mul_le (by omega), mul_comm k d]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have : k ≤ d * k := Nat.le_mul_of_pos_left k (by omega)
      exact ⟨by omega, h1, h2⟩
  rw [← hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold rng; split_ifs <;> simp

variable {q : ℕ} [NeZero q]

/-- **The units on a spline**: `|Σ_k w(k)1[(k, q) = 1] − (φ(q)/q)(B − A)| ≤ d(q)`. -/
theorem abs_spl_unit (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) :
    |∑ k ∈ supp A B ℓ r, spl A B ℓ r k * gU q k - (q.totient / q) * ((B - A : ℕ) : ℝ)| ≤ q.divisors.card := by
  have h := norm_Ew_spl_le (q := q) A B ℓ r hℓ
  have e : Ew (q := q) (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ)) =
      ((∑ k ∈ supp A B ℓ r, spl A B ℓ r k * gU q k - (q.totient / q) * ((B - A : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [Ew, ← sum_spl A B ℓ r hℓ]
    push_cast
    simp only [gU_cast]
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **The units in an interval**: `|Σ_{C<k≤D} 1[(k, q) = 1] − (φ(q)/q)(D − C)| ≤ d(q)`. -/
theorem abs_Ioc_unit (C D : ℕ) :
    |∑ k ∈ Ioc C D, gU q k - (q.totient / q) * ((D - C : ℕ) : ℝ)| ≤ q.divisors.card := by
  have h := norm_sum_Ioc_unit_le (q := q) C D
  have e : ∑ k ∈ Ioc C D, ((if IsUnit (k : ZMod q) then (1 : ℂ) else 0) - (q.totient : ℂ) / q) =
      ((∑ k ∈ Ioc C D, gU q k - (q.totient / q) * ((D - C : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    push_cast
    simp only [gU_cast]
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ### The main part of a leaf -/

/-- A spline's mass `B − A`. -/
noncomputable def massv (t : ℕ × ℕ × ℕ × ℕ) : ℝ := ((t.2.1 - t.1 : ℕ) : ℝ)

/-- The length `⌊N₂/d⌋ − ⌊N₁/d⌋` of the cofactors' range. -/
noncomputable def len (N₁ N₂ d : ℕ) : ℝ := ((N₂ / d - N₁ / d : ℕ) : ℝ)

omit [NeZero q] in
theorem ssum_gU (t : ℕ × ℕ × ℕ × ℕ) (d : ℕ) :
    ssum t (gU q) d = gU q d * ∑ k ∈ suppv t, splv t k * gU q k := by
  unfold ssum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [gU_mul]; ring

/-- `ssum(t, gU, d)` is `gU(d)(φ(q)/q)·mass` within `d(q)`. -/
theorem abs_ssum_gU (t : ℕ × ℕ × ℕ × ℕ) (ht : 1 ≤ t.2.2.1) (d : ℕ) :
    |ssum t (gU q) d - gU q d * ((q.totient / q) * massv t)| ≤ q.divisors.card := by
  rw [ssum_gU, ← mul_sub, abs_mul, abs_of_nonneg (gU_nonneg q d)]
  have h := abs_spl_unit (q := q) t.1 t.2.1 t.2.2.1 t.2.2.2 ht
  calc gU q d * |∑ k ∈ suppv t, splv t k * gU q k - (q.totient / q) * massv t|
      ≤ 1 * |∑ k ∈ suppv t, splv t k * gU q k - (q.totient / q) * massv t| :=
        mul_le_mul_of_nonneg_right (gU_le_one q d) (abs_nonneg _)
    _ ≤ q.divisors.card := by rw [one_mul]; exact h

/-- `rsum(gU, d)` is `gU(d)(φ(q)/q)·len` within `d(q)`, for `d ≥ 1`. -/
theorem abs_rsum_gU (N₁ N₂ d : ℕ) (hd : 1 ≤ d) :
    |rsum N₁ N₂ (gU q) d - gU q d * ((q.totient / q) * len N₁ N₂ d)| ≤ q.divisors.card := by
  have e : rsum N₁ N₂ (gU q) d = gU q d * ∑ k ∈ Ioc (N₁ / d) (N₂ / d), gU q k := by
    unfold rsum
    rw [Finset.mul_sum, ← sum_rng_eq N₁ N₂ d hd]
    exact Finset.sum_congr rfl fun k _ => by rw [gU_mul]
  rw [e, len, ← mul_sub, abs_mul, abs_of_nonneg (gU_nonneg q d)]
  have h := abs_Ioc_unit (q := q) (N₁ / d) (N₂ / d)
  calc gU q d * |∑ k ∈ Ioc (N₁ / d) (N₂ / d), gU q k - (q.totient / q) * ((N₂ / d - N₁ / d : ℕ) : ℝ)|
      ≤ 1 * |∑ k ∈ Ioc (N₁ / d) (N₂ / d), gU q k - (q.totient / q) * ((N₂ / d - N₁ / d : ℕ) : ℝ)| :=
        mul_le_mul_of_nonneg_right (gU_le_one q d) (abs_nonneg _)
    _ ≤ q.divisors.card := by rw [one_mul]; exact h

omit [NeZero q] in
/-- The masses of the splines around the range: `w⁻ ≤ rng(d, ·) ≤ w⁺` gives `mass⁻ ≤ len ≤ mass⁺`. -/
theorem mass_le_len (N₁ N₂ d : ℕ) (hd : 1 ≤ d) (tp tm : ℕ × ℕ × ℕ × ℕ) (hp : 1 ≤ tp.2.2.1) (hm : 1 ≤ tm.2.2.1)
    (hup : ∀ k, rng N₁ N₂ d k ≤ splv tp k) (hlo : ∀ k, splv tm k ≤ rng N₁ N₂ d k) :
    massv tm ≤ len N₁ N₂ d ∧ len N₁ N₂ d ≤ massv tp := by
  set K := range (N₂ + 1) ∪ suppv tp ∪ suppv tm with hK
  have hKr : range (N₂ + 1) ⊆ K := fun k hk => by rw [hK]; simp [hk]
  have hKp : suppv tp ⊆ K := fun k hk => by rw [hK]; simp [hk]
  have hKm : suppv tm ⊆ K := fun k hk => by rw [hK]; simp [hk]
  have elen : len N₁ N₂ d = ∑ k ∈ K, rng N₁ N₂ d k * 1 := by
    rw [sum_rng_superset N₁ N₂ d hd hKr, sum_rng_eq N₁ N₂ d hd, len, Finset.sum_const, Nat.card_Ioc, nsmul_one]
  have ep : massv tp = ∑ k ∈ K, splv tp k * 1 := by
    have h1 := sum_spl_superset tp.1 tp.2.1 tp.2.2.1 tp.2.2.2 hKp (fun _ => (1 : ℝ))
    have h2 := sum_spl tp.1 tp.2.1 tp.2.2.1 tp.2.2.2 hp
    simp only [mul_one] at h1 ⊢
    rw [massv, ← h2]
    exact h1.symm
  have em : massv tm = ∑ k ∈ K, splv tm k * 1 := by
    have h1 := sum_spl_superset tm.1 tm.2.1 tm.2.2.1 tm.2.2.2 hKm (fun _ => (1 : ℝ))
    have h2 := sum_spl tm.1 tm.2.1 tm.2.2.1 tm.2.2.2 hm
    simp only [mul_one] at h1 ⊢
    rw [massv, ← h2]
    exact h1.symm
  rw [elen, ep, em]
  exact ⟨Finset.sum_le_sum fun k _ => by rw [mul_one, mul_one]; exact hlo k,
    Finset.sum_le_sum fun k _ => by rw [mul_one, mul_one]; exact hup k⟩

omit [NeZero q] in
/-- `|⌊N₂/d⌋ − ⌊N₁/d⌋ − (N₂ − N₁)/d| ≤ 1` for `N₁ ≤ N₂` and `d ≥ 1`. -/
theorem abs_len_sub (N₁ N₂ d : ℕ) (hN : N₁ ≤ N₂) (hd : 1 ≤ d) :
    |len N₁ N₂ d - ((N₂ : ℝ) - N₁) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hle : N₁ / d ≤ N₂ / d := Nat.div_le_div_right hN
  have e1 := Nat.div_add_mod N₂ d
  have e2 := Nat.div_add_mod N₁ d
  have h1 : N₂ % d < d := Nat.mod_lt N₂ (by omega)
  have h2 : N₁ % d < d := Nat.mod_lt N₁ (by omega)
  have e : len N₁ N₂ d - ((N₂ : ℝ) - N₁) / d = (((N₁ % d : ℕ) : ℝ) - (N₂ % d : ℕ)) / d := by
    have e1' : (d : ℝ) * ((N₂ / d : ℕ) : ℝ) + ((N₂ % d : ℕ) : ℝ) = N₂ := by exact_mod_cast e1
    have e2' : (d : ℝ) * ((N₁ / d : ℕ) : ℝ) + ((N₁ % d : ℕ) : ℝ) = N₁ := by exact_mod_cast e2
    rw [len, Nat.cast_sub hle, eq_div_iff hdR.ne', sub_mul, div_mul_cancel₀ _ hdR.ne']
    linear_combination e1' - e2'
  rw [e, abs_div, abs_of_pos hdR, div_le_one hdR, abs_le]
  have h1' : ((N₂ % d : ℕ) : ℝ) < d := by exact_mod_cast h1
  have h2' : ((N₁ % d : ℕ) : ℝ) < d := by exact_mod_cast h2
  have h3 : (0 : ℝ) ≤ ((N₂ % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((N₁ % d : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

omit [NeZero q] in
/-- **One weight's main part, in the reals.** If `M⁻ ≤ L ≤ M⁺`, `0 ≤ g ≤ 1`, `c ≥ 0` and `x^± = gcM^±` within `D`, then
`λ₊x⁺ − λ₋x⁻ ≤ gc(λL + |λ|(M⁺ − M⁻)) + |λ|D` and `λ₊x⁻ − λ₋x⁺ ≥ gc(λL − |λ|(M⁺ − M⁻)) − |λ|D`. -/
theorem term_main (lam xp xm Mp Mm L g c D : ℝ) (hML : Mm ≤ L) (hLM : L ≤ Mp) (hg0 : 0 ≤ g) (hc : 0 ≤ c)
    (hp : |xp - g * c * Mp| ≤ D) (hm : |xm - g * c * Mm| ≤ D) :
    ppart lam * xp - npart lam * xm ≤ g * c * (lam * L + |lam| * (Mp - Mm)) + |lam| * D ∧
      g * c * (lam * L - |lam| * (Mp - Mm)) - |lam| * D ≤ ppart lam * xm - npart lam * xp := by
  have e := ppart_sub_npart lam
  have e' := ppart_add_npart lam
  have hpp := ppart_nonneg lam
  have hnn := npart_nonneg lam
  have hgc : 0 ≤ g * c := mul_nonneg hg0 hc
  rw [abs_le] at hp hm
  constructor
  · -- `λ₊x⁺ ≤ λ₊(gcM⁺ + D)` and `−λ₋x⁻ ≤ −λ₋(gcM⁻ − D)`
    have h1 : ppart lam * xp ≤ ppart lam * (g * c * Mp + D) := mul_le_mul_of_nonneg_left (by linarith) hpp
    have h2 : npart lam * (g * c * Mm - D) ≤ npart lam * xm := mul_le_mul_of_nonneg_left (by linarith) hnn
    have h3 : ppart lam * (g * c * (Mp - L)) ≤ ppart lam * (g * c * (Mp - Mm)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hgc) hpp
    have h4 : npart lam * (g * c * (L - Mm)) ≤ npart lam * (g * c * (Mp - Mm)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hgc) hnn
    have e2 : g * c * (lam * L + |lam| * (Mp - Mm)) + |lam| * D =
        ppart lam * (g * c * Mp + D) - npart lam * (g * c * Mm - D) +
          (ppart lam * (g * c * (Mp - Mm)) - ppart lam * (g * c * (Mp - L))) +
          (npart lam * (g * c * (Mp - Mm)) - npart lam * (g * c * (L - Mm))) := by
      linear_combination (-(g * c * L)) * e + (-(g * c * (Mp - Mm) + D)) * e'
    rw [e2]
    linarith
  · have h1 : ppart lam * (g * c * Mm - D) ≤ ppart lam * xm := mul_le_mul_of_nonneg_left (by linarith) hpp
    have h2 : npart lam * xp ≤ npart lam * (g * c * Mp + D) := mul_le_mul_of_nonneg_left (by linarith) hnn
    have h3 : ppart lam * (g * c * (L - Mm)) ≤ ppart lam * (g * c * (Mp - Mm)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hgc) hpp
    have h4 : npart lam * (g * c * (Mp - L)) ≤ npart lam * (g * c * (Mp - Mm)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hgc) hnn
    have e2 : g * c * (lam * L - |lam| * (Mp - Mm)) - |lam| * D =
        ppart lam * (g * c * Mm - D) - npart lam * (g * c * Mp + D) -
          (ppart lam * (g * c * (Mp - Mm)) - ppart lam * (g * c * (L - Mm))) -
          (npart lam * (g * c * (Mp - Mm)) - npart lam * (g * c * (Mp - L))) := by
      linear_combination (-(g * c * L)) * e + (g * c * (Mp - Mm) + D) * e'
    rw [e2]
    linarith

/-- **The main part of one leaf, above.** With `d = d₁d₂` and `d'_σ = d₁f_σd₂`, `leaf_upper`'s main part is at most
`((N₂ − N₁)/q)(Σ_σ λ_σ1[(d'_σ, q) = 1]/d'_σ − Σ_τ λ_τ1[(df_τ, q) = 1]/(df_τ))`
plus `q⁻¹(Σ_σ |λ_σ|(mass⁺_σ − mass⁻_σ + 1) + Σ_τ |λ_τ|)` and `(Σ_σ |λ_σ| + Σ_τ |λ_τ|)d(q)/φ(q)`. -/
theorem main_upper (N₁ N₂ d₁ d₂ : ℕ) (hN : N₁ ≤ N₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (tp tm : κ₁ → ℕ × ℕ × ℕ × ℕ) (htp : ∀ σ ∈ S₁, 1 ≤ (tp σ).2.2.1) (htm : ∀ σ ∈ S₁, 1 ≤ (tm σ).2.2.1)
    (hup : ∀ σ ∈ S₁, ∀ k, rng N₁ N₂ (d₁ * f₁ σ * d₂) k ≤ splv (tp σ) k)
    (hlo : ∀ σ ∈ S₁, ∀ k, splv (tm σ) k ≤ rng N₁ N₂ (d₁ * f₁ σ * d₂) k) :
    (∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp σ) (gU q) (d₁ * f₁ σ * d₂) -
          npart (l₁ σ) * ssum (tm σ) (gU q) (d₁ * f₁ σ * d₂)) -
        ∑ τ ∈ S₂, l₂ τ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₂ τ)) / q.totient ≤
      ((N₂ : ℝ) - N₁) / q * (∑ σ ∈ S₁, l₁ σ * gU q (d₁ * f₁ σ * d₂) / (d₁ * f₁ σ * d₂ : ℕ) -
          ∑ τ ∈ S₂, l₂ τ * gU q (d₁ * d₂ * f₂ τ) / (d₁ * d₂ * f₂ τ : ℕ)) +
        (∑ σ ∈ S₁, |l₁ σ| * (massv (tp σ) - massv (tm σ) + 1) + ∑ τ ∈ S₂, |l₂ τ|) / q +
        (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (q.divisors.card / q.totient) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  set c : ℝ := q.totient / q with hc
  have hc0 : 0 ≤ c := by positivity
  set D : ℝ := (q.divisors.card : ℝ) with hD
  set W : ℝ := (N₂ : ℝ) - N₁ with hW
  -- each weight above
  have hσ : ∀ σ ∈ S₁, ppart (l₁ σ) * ssum (tp σ) (gU q) (d₁ * f₁ σ * d₂) -
      npart (l₁ σ) * ssum (tm σ) (gU q) (d₁ * f₁ σ * d₂) ≤
      c * (l₁ σ * gU q (d₁ * f₁ σ * d₂) * W / (d₁ * f₁ σ * d₂ : ℕ) +
        |l₁ σ| * (massv (tp σ) - massv (tm σ) + 1)) + |l₁ σ| * D := by
    intro σ hσ
    set d' := d₁ * f₁ σ * d₂ with hd'
    have hd'1 : 1 ≤ d' := Nat.one_le_iff_ne_zero.2 (by have := hf₁ σ hσ; positivity)
    have hd'R : (0 : ℝ) < (d' : ℕ) := by exact_mod_cast (by omega : 0 < d')
    obtain ⟨hML, hLM⟩ := mass_le_len N₁ N₂ d' hd'1 (tp σ) (tm σ) (htp σ hσ) (htm σ hσ) (hup σ hσ) (hlo σ hσ)
    have hp := abs_ssum_gU (q := q) (tp σ) (htp σ hσ) d'
    have hm := abs_ssum_gU (q := q) (tm σ) (htm σ hσ) d'
    rw [show gU q d' * (q.totient / q * massv (tp σ)) = gU q d' * c * massv (tp σ) by rw [hc]; ring] at hp
    rw [show gU q d' * (q.totient / q * massv (tm σ)) = gU q d' * c * massv (tm σ) by rw [hc]; ring] at hm
    have h1 := (term_main (l₁ σ) _ _ _ _ _ _ c D hML hLM (gU_nonneg q d') hc0 hp hm).1
    -- `len` against `(N₂ − N₁)/d'`
    have hlen := abs_len_sub N₁ N₂ d' hN hd'1
    have hg1 := gU_le_one q d'
    have hg0 := gU_nonneg q d'
    have hΔ : 0 ≤ massv (tp σ) - massv (tm σ) := by linarith
    have h2 : gU q d' * (l₁ σ * len N₁ N₂ d') ≤ l₁ σ * gU q d' * W / d' + |l₁ σ| := by
      have e : gU q d' * (l₁ σ * len N₁ N₂ d') - l₁ σ * gU q d' * W / d' =
          gU q d' * l₁ σ * (len N₁ N₂ d' - W / d') := by ring
      have h3 : gU q d' * l₁ σ * (len N₁ N₂ d' - W / d') ≤ |l₁ σ| := by
        calc gU q d' * l₁ σ * (len N₁ N₂ d' - W / d') ≤ |gU q d' * l₁ σ * (len N₁ N₂ d' - W / d')| :=
              le_abs_self _
          _ = gU q d' * |l₁ σ| * |len N₁ N₂ d' - W / d'| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg0]
          _ ≤ 1 * |l₁ σ| * 1 := by
              gcongr
          _ = |l₁ σ| := by ring
      linarith
    have h4 : gU q d' * (|l₁ σ| * (massv (tp σ) - massv (tm σ))) ≤ |l₁ σ| * (massv (tp σ) - massv (tm σ)) :=
      mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) hΔ) hg1
    calc ppart (l₁ σ) * ssum (tp σ) (gU q) d' - npart (l₁ σ) * ssum (tm σ) (gU q) d'
        ≤ gU q d' * c * (l₁ σ * len N₁ N₂ d' + |l₁ σ| * (massv (tp σ) - massv (tm σ))) + |l₁ σ| * D := h1
      _ = c * (gU q d' * (l₁ σ * len N₁ N₂ d') + gU q d' * (|l₁ σ| * (massv (tp σ) - massv (tm σ)))) +
          |l₁ σ| * D := by ring
      _ ≤ c * (l₁ σ * gU q d' * W / d' + |l₁ σ| + |l₁ σ| * (massv (tp σ) - massv (tm σ))) + |l₁ σ| * D := by
          gcongr
      _ = c * (l₁ σ * gU q d' * W / (d₁ * f₁ σ * d₂ : ℕ) + |l₁ σ| * (massv (tp σ) - massv (tm σ) + 1)) +
          |l₁ σ| * D := by rw [hd']; ring
  -- each weight below
  have hτ : ∀ τ ∈ S₂, -(l₂ τ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₂ τ)) ≤
      c * (-(l₂ τ * gU q (d₁ * d₂ * f₂ τ) * W / (d₁ * d₂ * f₂ τ : ℕ)) + |l₂ τ|) + |l₂ τ| * D := by
    intro τ hτ
    set d' := d₁ * d₂ * f₂ τ with hd'
    have hd'1 : 1 ≤ d' := Nat.one_le_iff_ne_zero.2 (by have := hf₂ τ hτ; positivity)
    have hr := abs_rsum_gU (q := q) N₁ N₂ d' hd'1
    have hlen := abs_len_sub N₁ N₂ d' hN hd'1
    have hg1 := gU_le_one q d'
    have hg0 := gU_nonneg q d'
    rw [abs_le] at hr
    have h1 : -(l₂ τ * rsum N₁ N₂ (gU q) d') ≤ -(l₂ τ * (gU q d' * (c * len N₁ N₂ d'))) + |l₂ τ| * D := by
      have : |l₂ τ * (rsum N₁ N₂ (gU q) d' - gU q d' * (c * len N₁ N₂ d'))| ≤ |l₂ τ| * D := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩) (abs_nonneg _)
      have := neg_abs_le (l₂ τ * (rsum N₁ N₂ (gU q) d' - gU q d' * (c * len N₁ N₂ d')))
      nlinarith
    have h2 : -(gU q d' * l₂ τ * len N₁ N₂ d') ≤ -(gU q d' * l₂ τ * W / d') + |l₂ τ| := by
      have e : gU q d' * l₂ τ * W / d' - gU q d' * l₂ τ * len N₁ N₂ d' =
          gU q d' * l₂ τ * (W / d' - len N₁ N₂ d') := by ring
      have h3 : gU q d' * l₂ τ * (W / d' - len N₁ N₂ d') ≤ |l₂ τ| := by
        calc gU q d' * l₂ τ * (W / d' - len N₁ N₂ d') ≤ |gU q d' * l₂ τ * (W / d' - len N₁ N₂ d')| :=
              le_abs_self _
          _ = gU q d' * |l₂ τ| * |len N₁ N₂ d' - W / d'| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_sub_comm]
          _ ≤ 1 * |l₂ τ| * 1 := by
              gcongr
          _ = |l₂ τ| := by ring
      linarith
    have h5 : c * (-(gU q d' * l₂ τ * len N₁ N₂ d')) ≤ c * (-(gU q d' * l₂ τ * W / d') + |l₂ τ|) :=
      mul_le_mul_of_nonneg_left h2 hc0
    calc -(l₂ τ * rsum N₁ N₂ (gU q) d') ≤ -(l₂ τ * (gU q d' * (c * len N₁ N₂ d'))) + |l₂ τ| * D := h1
      _ = c * (-(gU q d' * l₂ τ * len N₁ N₂ d')) + |l₂ τ| * D := by ring
      _ ≤ c * (-(gU q d' * l₂ τ * W / d') + |l₂ τ|) + |l₂ τ| * D := by linarith
      _ = c * (-(l₂ τ * gU q d' * W / (d₁ * d₂ * f₂ τ : ℕ)) + |l₂ τ|) + |l₂ τ| * D := by rw [hd']; ring
  -- sum and divide by `φ(q)`
  have hsum := add_le_add (Finset.sum_le_sum hσ) (Finset.sum_le_sum hτ)
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg] at hsum
  rw [div_le_iff₀ hφ]
  refine hsum.trans (le_of_eq ?_)
  have hS1 : ∑ σ ∈ S₁, (c * (l₁ σ * gU q (d₁ * f₁ σ * d₂) * W / (d₁ * f₁ σ * d₂ : ℕ) +
        |l₁ σ| * (massv (tp σ) - massv (tm σ) + 1)) + |l₁ σ| * D) =
      c * W * (∑ σ ∈ S₁, l₁ σ * gU q (d₁ * f₁ σ * d₂) / (d₁ * f₁ σ * d₂ : ℕ)) +
        c * (∑ σ ∈ S₁, |l₁ σ| * (massv (tp σ) - massv (tm σ) + 1)) + D * ∑ σ ∈ S₁, |l₁ σ| := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have hS2 : ∑ τ ∈ S₂, (c * (-(l₂ τ * gU q (d₁ * d₂ * f₂ τ) * W / (d₁ * d₂ * f₂ τ : ℕ)) + |l₂ τ|) +
        |l₂ τ| * D) =
      -(c * W * ∑ τ ∈ S₂, l₂ τ * gU q (d₁ * d₂ * f₂ τ) / (d₁ * d₂ * f₂ τ : ℕ)) +
        c * (∑ τ ∈ S₂, |l₂ τ|) + D * ∑ τ ∈ S₂, |l₂ τ| := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hS1, hS2, hc, hD, hW]
  field_simp
  ring

/-- **The main part of one leaf, below.** `leaf_lower`'s main part is at least
`((N₂ − N₁)/q)(Σ_τ λ_τ1[(d'_τ, q) = 1]/d'_τ − Σ_σ λ_σ1[(df_σ, q) = 1]/(df_σ))`, `d'_τ = d₁f_τd₂`, less
`q⁻¹(Σ_τ |λ_τ|(mass⁺_τ − mass⁻_τ + 1) + Σ_σ |λ_σ|)` and `(Σ_τ |λ_τ| + Σ_σ |λ_σ|)d(q)/φ(q)`. -/
theorem main_lower (N₁ N₂ d₁ d₂ : ℕ) (hN : N₁ ≤ N₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (tp tm : κ₂ → ℕ × ℕ × ℕ × ℕ) (htp : ∀ τ ∈ S₂, 1 ≤ (tp τ).2.2.1) (htm : ∀ τ ∈ S₂, 1 ≤ (tm τ).2.2.1)
    (hup : ∀ τ ∈ S₂, ∀ k, rng N₁ N₂ (d₁ * f₂ τ * d₂) k ≤ splv (tp τ) k)
    (hlo : ∀ τ ∈ S₂, ∀ k, splv (tm τ) k ≤ rng N₁ N₂ (d₁ * f₂ τ * d₂) k) :
    ((N₂ : ℝ) - N₁) / q * (∑ τ ∈ S₂, l₂ τ * gU q (d₁ * f₂ τ * d₂) / (d₁ * f₂ τ * d₂ : ℕ) -
          ∑ σ ∈ S₁, l₁ σ * gU q (d₁ * d₂ * f₁ σ) / (d₁ * d₂ * f₁ σ : ℕ)) -
        (∑ τ ∈ S₂, |l₂ τ| * (massv (tp τ) - massv (tm τ) + 1) + ∑ σ ∈ S₁, |l₁ σ|) / q -
        (∑ τ ∈ S₂, |l₂ τ| + ∑ σ ∈ S₁, |l₁ σ|) * (q.divisors.card / q.totient) ≤
      (∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm τ) (gU q) (d₁ * f₂ τ * d₂) -
          npart (l₂ τ) * ssum (tp τ) (gU q) (d₁ * f₂ τ * d₂)) -
        ∑ σ ∈ S₁, l₁ σ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₁ σ)) / q.totient := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  set c : ℝ := q.totient / q with hc
  have hc0 : 0 ≤ c := by positivity
  set D : ℝ := (q.divisors.card : ℝ) with hD
  set W : ℝ := (N₂ : ℝ) - N₁ with hW
  -- each weight below, with its splines
  have hτ : ∀ τ ∈ S₂, c * (l₂ τ * gU q (d₁ * f₂ τ * d₂) * W / (d₁ * f₂ τ * d₂ : ℕ) -
        |l₂ τ| * (massv (tp τ) - massv (tm τ) + 1)) - |l₂ τ| * D ≤
      ppart (l₂ τ) * ssum (tm τ) (gU q) (d₁ * f₂ τ * d₂) - npart (l₂ τ) * ssum (tp τ) (gU q) (d₁ * f₂ τ * d₂) := by
    intro τ hτ
    set d' := d₁ * f₂ τ * d₂ with hd'
    have hd'1 : 1 ≤ d' := Nat.one_le_iff_ne_zero.2 (by have := hf₂ τ hτ; positivity)
    obtain ⟨hML, hLM⟩ := mass_le_len N₁ N₂ d' hd'1 (tp τ) (tm τ) (htp τ hτ) (htm τ hτ) (hup τ hτ) (hlo τ hτ)
    have hp := abs_ssum_gU (q := q) (tp τ) (htp τ hτ) d'
    have hm := abs_ssum_gU (q := q) (tm τ) (htm τ hτ) d'
    rw [show gU q d' * (q.totient / q * massv (tp τ)) = gU q d' * c * massv (tp τ) by rw [hc]; ring] at hp
    rw [show gU q d' * (q.totient / q * massv (tm τ)) = gU q d' * c * massv (tm τ) by rw [hc]; ring] at hm
    have h1 := (term_main (l₂ τ) _ _ _ _ _ _ c D hML hLM (gU_nonneg q d') hc0 hp hm).2
    have hlen := abs_len_sub N₁ N₂ d' hN hd'1
    have hg1 := gU_le_one q d'
    have hg0 := gU_nonneg q d'
    have hΔ : 0 ≤ massv (tp τ) - massv (tm τ) := by linarith
    have h2 : l₂ τ * gU q d' * W / d' - |l₂ τ| ≤ gU q d' * (l₂ τ * len N₁ N₂ d') := by
      have e : l₂ τ * gU q d' * W / d' - gU q d' * (l₂ τ * len N₁ N₂ d') =
          gU q d' * l₂ τ * (W / d' - len N₁ N₂ d') := by ring
      have h3 : gU q d' * l₂ τ * (W / d' - len N₁ N₂ d') ≤ |l₂ τ| := by
        calc gU q d' * l₂ τ * (W / d' - len N₁ N₂ d') ≤ |gU q d' * l₂ τ * (W / d' - len N₁ N₂ d')| :=
              le_abs_self _
          _ = gU q d' * |l₂ τ| * |len N₁ N₂ d' - W / d'| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_sub_comm]
          _ ≤ 1 * |l₂ τ| * 1 := by
              gcongr
          _ = |l₂ τ| := by ring
      linarith
    have h4 : gU q d' * (|l₂ τ| * (massv (tp τ) - massv (tm τ))) ≤ |l₂ τ| * (massv (tp τ) - massv (tm τ)) :=
      mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) hΔ) hg1
    calc c * (l₂ τ * gU q d' * W / (d₁ * f₂ τ * d₂ : ℕ) - |l₂ τ| * (massv (tp τ) - massv (tm τ) + 1)) -
          |l₂ τ| * D
        = c * (l₂ τ * gU q d' * W / d' - |l₂ τ| - |l₂ τ| * (massv (tp τ) - massv (tm τ))) - |l₂ τ| * D := by
          rw [hd']; ring
      _ ≤ c * (gU q d' * (l₂ τ * len N₁ N₂ d') - gU q d' * (|l₂ τ| * (massv (tp τ) - massv (tm τ)))) -
          |l₂ τ| * D := by
          gcongr
      _ = gU q d' * c * (l₂ τ * len N₁ N₂ d' - |l₂ τ| * (massv (tp τ) - massv (tm τ))) - |l₂ τ| * D := by ring
      _ ≤ ppart (l₂ τ) * ssum (tm τ) (gU q) d' - npart (l₂ τ) * ssum (tp τ) (gU q) d' := h1
  -- each weight above, by its count
  have hσ : ∀ σ ∈ S₁, c * (-(l₁ σ * gU q (d₁ * d₂ * f₁ σ) * W / (d₁ * d₂ * f₁ σ : ℕ)) - |l₁ σ|) - |l₁ σ| * D ≤
      -(l₁ σ * rsum N₁ N₂ (gU q) (d₁ * d₂ * f₁ σ)) := by
    intro σ hσ
    set d' := d₁ * d₂ * f₁ σ with hd'
    have hd'1 : 1 ≤ d' := Nat.one_le_iff_ne_zero.2 (by have := hf₁ σ hσ; positivity)
    have hr := abs_rsum_gU (q := q) N₁ N₂ d' hd'1
    have hlen := abs_len_sub N₁ N₂ d' hN hd'1
    have hg1 := gU_le_one q d'
    have hg0 := gU_nonneg q d'
    have h1 : -(l₁ σ * (gU q d' * (c * len N₁ N₂ d'))) - |l₁ σ| * D ≤ -(l₁ σ * rsum N₁ N₂ (gU q) d') := by
      have : |l₁ σ * (rsum N₁ N₂ (gU q) d' - gU q d' * (c * len N₁ N₂ d'))| ≤ |l₁ σ| * D := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [hc]; exact hr
      have := le_abs_self (l₁ σ * (rsum N₁ N₂ (gU q) d' - gU q d' * (c * len N₁ N₂ d')))
      nlinarith
    have h2 : -(gU q d' * l₁ σ * W / d') - |l₁ σ| ≤ -(gU q d' * l₁ σ * len N₁ N₂ d') := by
      have h3 : gU q d' * l₁ σ * (len N₁ N₂ d' - W / d') ≤ |l₁ σ| := by
        calc gU q d' * l₁ σ * (len N₁ N₂ d' - W / d') ≤ |gU q d' * l₁ σ * (len N₁ N₂ d' - W / d')| :=
              le_abs_self _
          _ = gU q d' * |l₁ σ| * |len N₁ N₂ d' - W / d'| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg0]
          _ ≤ 1 * |l₁ σ| * 1 := by
              gcongr
          _ = |l₁ σ| := by ring
      have e : gU q d' * l₁ σ * len N₁ N₂ d' - gU q d' * l₁ σ * W / d' =
          gU q d' * l₁ σ * (len N₁ N₂ d' - W / d') := by ring
      linarith
    have h5 : c * (-(gU q d' * l₁ σ * W / d') - |l₁ σ|) ≤ c * (-(gU q d' * l₁ σ * len N₁ N₂ d')) :=
      mul_le_mul_of_nonneg_left h2 hc0
    calc c * (-(l₁ σ * gU q d' * W / (d₁ * d₂ * f₁ σ : ℕ)) - |l₁ σ|) - |l₁ σ| * D
        = c * (-(gU q d' * l₁ σ * W / d') - |l₁ σ|) - |l₁ σ| * D := by rw [hd']; ring
      _ ≤ c * (-(gU q d' * l₁ σ * len N₁ N₂ d')) - |l₁ σ| * D := by linarith
      _ = -(l₁ σ * (gU q d' * (c * len N₁ N₂ d'))) - |l₁ σ| * D := by ring
      _ ≤ -(l₁ σ * rsum N₁ N₂ (gU q) d') := h1
  -- sum and divide by `φ(q)`
  have hsum := add_le_add (Finset.sum_le_sum hτ) (Finset.sum_le_sum hσ)
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg] at hsum
  rw [le_div_iff₀ hφ]
  refine le_trans (le_of_eq ?_) hsum
  have hS1 : ∑ τ ∈ S₂, (c * (l₂ τ * gU q (d₁ * f₂ τ * d₂) * W / (d₁ * f₂ τ * d₂ : ℕ) -
        |l₂ τ| * (massv (tp τ) - massv (tm τ) + 1)) - |l₂ τ| * D) =
      c * W * (∑ τ ∈ S₂, l₂ τ * gU q (d₁ * f₂ τ * d₂) / (d₁ * f₂ τ * d₂ : ℕ)) -
        c * (∑ τ ∈ S₂, |l₂ τ| * (massv (tp τ) - massv (tm τ) + 1)) - D * ∑ τ ∈ S₂, |l₂ τ| := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  have hS2 : ∑ σ ∈ S₁, (c * (-(l₁ σ * gU q (d₁ * d₂ * f₁ σ) * W / (d₁ * d₂ * f₁ σ : ℕ)) - |l₁ σ|) -
        |l₁ σ| * D) =
      -(c * W * ∑ σ ∈ S₁, l₁ σ * gU q (d₁ * d₂ * f₁ σ) / (d₁ * d₂ * f₁ σ : ℕ)) -
        c * (∑ σ ∈ S₁, |l₁ σ|) - D * ∑ σ ∈ S₁, |l₁ σ| := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hS1, hS2, hc, hD, hW]
  field_simp
  ring

/-! ### A family of leaves -/

omit [NeZero q] in
/-- The gap at `d`: `Σ_σ λ_σ1[(df_σ, q) = 1]/(df_σ) − Σ_τ λ_τ1[(df_τ, q) = 1]/(df_τ)` is `1[(d, q) = 1]Γ/d` with the
sieve's gap `Γ = Σ_σ λ_σ1[(f_σ, q) = 1]/f_σ − Σ_τ λ_τ1[(f_τ, q) = 1]/f_τ`, so at most `|Γ|/d` in size. -/
theorem abs_gap_le (d : ℕ) (hd : 1 ≤ d) {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ)
    (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ) (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ) :
    |∑ σ ∈ S₁, l₁ σ * gU q (d * f₁ σ) / (d * f₁ σ : ℕ) - ∑ τ ∈ S₂, l₂ τ * gU q (d * f₂ τ) / (d * f₂ τ : ℕ)| ≤
      |∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have e : ∑ σ ∈ S₁, l₁ σ * gU q (d * f₁ σ) / (d * f₁ σ : ℕ) - ∑ τ ∈ S₂, l₂ τ * gU q (d * f₂ τ) / (d * f₂ τ : ℕ) =
      gU q d / d * (∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun σ hσ => ?_
      have : (0 : ℝ) < f₁ σ := by exact_mod_cast (by have := hf₁ σ hσ; omega : 0 < f₁ σ)
      rw [gU_mul]; push_cast; field_simp
    · refine Finset.sum_congr rfl fun τ hτ => ?_
      have : (0 : ℝ) < f₂ τ := by exact_mod_cast (by have := hf₂ τ hτ; omega : 0 < f₂ τ)
      rw [gU_mul]; push_cast; field_simp
  rw [e, abs_mul, abs_div, abs_of_nonneg (gU_nonneg q d), abs_of_pos hdR, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hdR]
  exact mul_le_of_le_one_left (abs_nonneg _) (gU_le_one q d)

/-- The main errors of one leaf: `(N₂ − N₁)/q·|Γ|/d` and the errors of `main_upper` and `main_lower`. -/
noncomputable def errL (q N₁ N₂ d : ℕ) {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (tp₁ tm₁ : κ₁ → ℕ × ℕ × ℕ × ℕ) (tp₂ tm₂ : κ₂ → ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ((N₂ : ℝ) - N₁) / q * (|∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| / d) +
    ((∑ σ ∈ S₁, |l₁ σ| * (massv (tp₁ σ) - massv (tm₁ σ) + 1) + ∑ τ ∈ S₂, |l₂ τ|) / q +
      (∑ τ ∈ S₂, |l₂ τ| * (massv (tp₂ τ) - massv (tm₂ τ) + 1) + ∑ σ ∈ S₁, |l₁ σ|) / q +
      2 * (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (q.divisors.card / q.totient))

/-- The bilinear part above of one leaf: `Σ_σ (λ₊ssum⁺(dw) − λ₋ssum⁻(dw))` at `d₁f_σd₂`. -/
noncomputable def dwU (q : ℕ) (a : ZMod q) (d₁ d₂ : ℕ) {κ₁ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ)
    (tp₁ tm₁ : κ₁ → ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ∑ σ ∈ S₁, (ppart (l₁ σ) * ssum (tp₁ σ) (dwR q a) (d₁ * f₁ σ * d₂) -
    npart (l₁ σ) * ssum (tm₁ σ) (dwR q a) (d₁ * f₁ σ * d₂))

/-- The bilinear part below of one leaf: `Σ_τ (λ₊ssum⁻(dw) − λ₋ssum⁺(dw))` at `d₁f_τd₂`. -/
noncomputable def dwL (q : ℕ) (a : ZMod q) (d₁ d₂ : ℕ) {κ₂ : Type*} (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ)
    (tp₂ tm₂ : κ₂ → ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ∑ τ ∈ S₂, (ppart (l₂ τ) * ssum (tm₂ τ) (dwR q a) (d₁ * f₂ τ * d₂) -
    npart (l₂ τ) * ssum (tp₂ τ) (dwR q a) (d₁ * f₂ τ * d₂))

/-- **One leaf, both ways**: its sum lies in `[−err + dwL, err + dwU]`. -/
theorem leaf_two_sided (a : ZMod q) (N₁ N₂ : ℕ) (hN : N₁ ≤ N₂) (d₁ d₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (R : ℕ → ℝ) {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (hR₁ : ∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (hR₂ : ∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m)
    (tp₁ tm₁ : κ₁ → ℕ × ℕ × ℕ × ℕ) (tp₂ tm₂ : κ₂ → ℕ × ℕ × ℕ × ℕ)
    (hℓ₁ : ∀ σ ∈ S₁, 1 ≤ (tp₁ σ).2.2.1 ∧ 1 ≤ (tm₁ σ).2.2.1) (hℓ₂ : ∀ τ ∈ S₂, 1 ≤ (tp₂ τ).2.2.1 ∧ 1 ≤ (tm₂ τ).2.2.1)
    (hsp₁ : ∀ σ ∈ S₁, ∀ k, splv (tm₁ σ) k ≤ rng N₁ N₂ (d₁ * f₁ σ * d₂) k ∧
      rng N₁ N₂ (d₁ * f₁ σ * d₂) k ≤ splv (tp₁ σ) k)
    (hsp₂ : ∀ τ ∈ S₂, ∀ k, splv (tm₂ τ) k ≤ rng N₁ N₂ (d₁ * f₂ τ * d₂) k ∧
      rng N₁ N₂ (d₁ * f₂ τ * d₂) k ≤ splv (tp₂ τ) k) :
    ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * dwR q a (d₁ * d₂ * m) ≤
        errL q N₁ N₂ (d₁ * d₂) S₁ f₁ l₁ S₂ f₂ l₂ tp₁ tm₁ tp₂ tm₂ + dwU q a d₁ d₂ S₁ f₁ l₁ tp₁ tm₁ ∧
      -errL q N₁ N₂ (d₁ * d₂) S₁ f₁ l₁ S₂ f₂ l₂ tp₁ tm₁ tp₂ tm₂ + dwL q a d₁ d₂ S₂ f₂ l₂ tp₂ tm₂ ≤
        ∑ m ∈ range (N₂ + 1), rng N₁ N₂ (d₁ * d₂) m * R m * dwR q a (d₁ * d₂ * m) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hW0 : (0 : ℝ) ≤ (N₂ : ℝ) - N₁ := sub_nonneg.2 (by exact_mod_cast hN)
  have hd : 1 ≤ d₁ * d₂ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hup := leaf_upper q a N₁ N₂ d₁ d₂ hd₁ hd₂ R S₁ f₁ l₁ hf₁ hR₁ S₂ f₂ l₂ hf₂ hR₂ tp₁ tm₁
    (fun σ hσ k => (hsp₁ σ hσ k).2) (fun σ hσ k => (hsp₁ σ hσ k).1)
  have hlo := leaf_lower q a N₁ N₂ d₁ d₂ hd₁ hd₂ R S₁ f₁ l₁ hf₁ hR₁ S₂ f₂ l₂ hf₂ hR₂ tp₂ tm₂
    (fun τ hτ k => (hsp₂ τ hτ k).2) (fun τ hτ k => (hsp₂ τ hτ k).1)
  have hmu := main_upper (q := q) N₁ N₂ d₁ d₂ hN hd₁ hd₂ S₁ f₁ l₁ hf₁ S₂ f₂ l₂ hf₂ tp₁ tm₁
    (fun σ hσ => (hℓ₁ σ hσ).1) (fun σ hσ => (hℓ₁ σ hσ).2) (fun σ hσ k => (hsp₁ σ hσ k).2)
    (fun σ hσ k => (hsp₁ σ hσ k).1)
  have hml := main_lower (q := q) N₁ N₂ d₁ d₂ hN hd₁ hd₂ S₁ f₁ l₁ hf₁ S₂ f₂ l₂ hf₂ tp₂ tm₂
    (fun τ hτ => (hℓ₂ τ hτ).1) (fun τ hτ => (hℓ₂ τ hτ).2) (fun τ hτ k => (hsp₂ τ hτ k).2)
    (fun τ hτ k => (hsp₂ τ hτ k).1)
  have hgap := abs_gap_le (q := q) (d₁ * d₂) hd S₁ f₁ l₁ hf₁ S₂ f₂ l₂ hf₂
  have eG1 : ∑ σ ∈ S₁, l₁ σ * gU q (d₁ * f₁ σ * d₂) / (d₁ * f₁ σ * d₂ : ℕ) =
      ∑ σ ∈ S₁, l₁ σ * gU q (d₁ * d₂ * f₁ σ) / (d₁ * d₂ * f₁ σ : ℕ) :=
    Finset.sum_congr rfl fun σ _ => by rw [show d₁ * f₁ σ * d₂ = d₁ * d₂ * f₁ σ by ring]
  have eG2 : ∑ τ ∈ S₂, l₂ τ * gU q (d₁ * f₂ τ * d₂) / (d₁ * f₂ τ * d₂ : ℕ) =
      ∑ τ ∈ S₂, l₂ τ * gU q (d₁ * d₂ * f₂ τ) / (d₁ * d₂ * f₂ τ : ℕ) :=
    Finset.sum_congr rfl fun τ _ => by rw [show d₁ * f₂ τ * d₂ = d₁ * d₂ * f₂ τ by ring]
  rw [eG1] at hmu
  rw [eG2] at hml
  set G := ∑ σ ∈ S₁, l₁ σ * gU q (d₁ * d₂ * f₁ σ) / (d₁ * d₂ * f₁ σ : ℕ) -
    ∑ τ ∈ S₂, l₂ τ * gU q (d₁ * d₂ * f₂ τ) / (d₁ * d₂ * f₂ τ : ℕ) with hG
  set Γa := |∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| with hΓa
  have hWq : (0 : ℝ) ≤ ((N₂ : ℝ) - N₁) / q := div_nonneg hW0 hq.le
  have hGl : ((N₂ : ℝ) - N₁) / q * G ≤ ((N₂ : ℝ) - N₁) / q * (Γa / (d₁ * d₂ : ℕ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self G).trans hgap) hWq
  have hGr : ((N₂ : ℝ) - N₁) / q * (-G) ≤ ((N₂ : ℝ) - N₁) / q * (Γa / (d₁ * d₂ : ℕ)) :=
    mul_le_mul_of_nonneg_left ((neg_le_abs G).trans hgap) hWq
  have eneg : ((N₂ : ℝ) - N₁) / q * (∑ τ ∈ S₂, l₂ τ * gU q (d₁ * d₂ * f₂ τ) / (d₁ * d₂ * f₂ τ : ℕ) -
      ∑ σ ∈ S₁, l₁ σ * gU q (d₁ * d₂ * f₁ σ) / (d₁ * d₂ * f₁ σ : ℕ)) = ((N₂ : ℝ) - N₁) / q * (-G) := by
    rw [hG]; ring
  rw [eneg] at hml
  have ecomm : (∑ τ ∈ S₂, |l₂ τ| + ∑ σ ∈ S₁, |l₁ σ|) = (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) := add_comm _ _
  rw [ecomm] at hml
  have hD0 : (0 : ℝ) ≤ (∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (q.divisors.card / q.totient) := by positivity
  have hm1 : 0 ≤ (∑ σ ∈ S₁, |l₁ σ| * (massv (tp₁ σ) - massv (tm₁ σ) + 1) + ∑ τ ∈ S₂, |l₂ τ|) / q := by
    refine div_nonneg (add_nonneg (Finset.sum_nonneg fun σ hσ => mul_nonneg (abs_nonneg _) ?_)
      (Finset.sum_nonneg fun τ _ => abs_nonneg _)) hq.le
    obtain ⟨h1, h2⟩ := mass_le_len N₁ N₂ _ (Nat.one_le_iff_ne_zero.2 (by have := hf₁ σ hσ; positivity))
      _ _ (hℓ₁ σ hσ).1 (hℓ₁ σ hσ).2 (fun k => (hsp₁ σ hσ k).2) (fun k => (hsp₁ σ hσ k).1)
    linarith
  have hm2 : 0 ≤ (∑ τ ∈ S₂, |l₂ τ| * (massv (tp₂ τ) - massv (tm₂ τ) + 1) + ∑ σ ∈ S₁, |l₁ σ|) / q := by
    refine div_nonneg (add_nonneg (Finset.sum_nonneg fun τ hτ => mul_nonneg (abs_nonneg _) ?_)
      (Finset.sum_nonneg fun σ _ => abs_nonneg _)) hq.le
    obtain ⟨h1, h2⟩ := mass_le_len N₁ N₂ _ (Nat.one_le_iff_ne_zero.2 (by have := hf₂ τ hτ; positivity))
      _ _ (hℓ₂ τ hτ).1 (hℓ₂ τ hτ).2 (fun k => (hsp₂ τ hτ k).2) (fun k => (hsp₂ τ hτ k).1)
    linarith
  have herr : errL q N₁ N₂ (d₁ * d₂) S₁ f₁ l₁ S₂ f₂ l₂ tp₁ tm₁ tp₂ tm₂ =
      ((N₂ : ℝ) - N₁) / q * (Γa / (d₁ * d₂ : ℕ)) +
        ((∑ σ ∈ S₁, |l₁ σ| * (massv (tp₁ σ) - massv (tm₁ σ) + 1) + ∑ τ ∈ S₂, |l₂ τ|) / q +
          (∑ τ ∈ S₂, |l₂ τ| * (massv (tp₂ τ) - massv (tm₂ τ) + 1) + ∑ σ ∈ S₁, |l₁ σ|) / q +
          2 * ((∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ|) * (q.divisors.card / q.totient))) := by
    rw [errL, hΓa]; ring
  rw [herr, dwU, dwL]
  constructor
  · linarith
  · linarith

/-- **The family of leaves.** Let the leaves `(y₁, y₂)` have values `d = π₁(y₁)π₂(y₂) ≥ 1` and weights `c ≥ 0`, let the
sieve weights `S₁` above and `S₂` below sandwich `R`, and let each leaf and weight have splines `w⁻ ≤ rng ≤ w⁺` at
`π₁fπ₂`. Then `|Σ_{y₁,y₂} c Σ_{m≤N₂} rng(d, m)R(m)dw(dm)|` is at most `Σ_y c·errL` plus the two bilinear parts
`|Σ_y c·dwU| + |Σ_y c·dwL|`. -/
theorem leaves_bound (a : ZMod q) (N₁ N₂ : ℕ) (hN : N₁ ≤ N₂) {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (hπ₁ : ∀ y ∈ Y₁, 1 ≤ π₁ y) (hπ₂ : ∀ y ∈ Y₂, 1 ≤ π₂ y)
    (c : ι₁ → ι₂ → ℝ) (hc : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, 0 ≤ c y₁ y₂) (R : ℕ → ℝ)
    {κ₁ κ₂ : Type*} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (hf₁ : ∀ σ ∈ S₁, 1 ≤ f₁ σ)
    (hR₁ : ∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m)
    (S₂ : Finset κ₂) (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ) (hf₂ : ∀ τ ∈ S₂, 1 ≤ f₂ τ)
    (hR₂ : ∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m)
    (tp₁ tm₁ : ι₁ → ι₂ → κ₁ → ℕ × ℕ × ℕ × ℕ) (tp₂ tm₂ : ι₁ → ι₂ → κ₂ → ℕ × ℕ × ℕ × ℕ)
    (hℓ₁ : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ σ ∈ S₁, 1 ≤ (tp₁ y₁ y₂ σ).2.2.1 ∧ 1 ≤ (tm₁ y₁ y₂ σ).2.2.1)
    (hℓ₂ : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ τ ∈ S₂, 1 ≤ (tp₂ y₁ y₂ τ).2.2.1 ∧ 1 ≤ (tm₂ y₁ y₂ τ).2.2.1)
    (hsp₁ : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ σ ∈ S₁, ∀ k,
      splv (tm₁ y₁ y₂ σ) k ≤ rng N₁ N₂ (π₁ y₁ * f₁ σ * π₂ y₂) k ∧
        rng N₁ N₂ (π₁ y₁ * f₁ σ * π₂ y₂) k ≤ splv (tp₁ y₁ y₂ σ) k)
    (hsp₂ : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ τ ∈ S₂, ∀ k,
      splv (tm₂ y₁ y₂ τ) k ≤ rng N₁ N₂ (π₁ y₁ * f₂ τ * π₂ y₂) k ∧
        rng N₁ N₂ (π₁ y₁ * f₂ τ * π₂ y₂) k ≤ splv (tp₂ y₁ y₂ τ) k) :
    |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * ∑ m ∈ range (N₂ + 1),
        rng N₁ N₂ (π₁ y₁ * π₂ y₂) m * R m * dwR q a (π₁ y₁ * π₂ y₂ * m)| ≤
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ *
          errL q N₁ N₂ (π₁ y₁ * π₂ y₂) S₁ f₁ l₁ S₂ f₂ l₂ (tp₁ y₁ y₂) (tm₁ y₁ y₂) (tp₂ y₁ y₂) (tm₂ y₁ y₂) +
        |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwU q a (π₁ y₁) (π₂ y₂) S₁ f₁ l₁ (tp₁ y₁ y₂) (tm₁ y₁ y₂)| +
        |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwL q a (π₁ y₁) (π₂ y₂) S₂ f₂ l₂ (tp₂ y₁ y₂) (tm₂ y₁ y₂)| := by
  set X := ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * ∑ m ∈ range (N₂ + 1),
    rng N₁ N₂ (π₁ y₁ * π₂ y₂) m * R m * dwR q a (π₁ y₁ * π₂ y₂ * m) with hX
  set M := ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ *
    errL q N₁ N₂ (π₁ y₁ * π₂ y₂) S₁ f₁ l₁ S₂ f₂ l₂ (tp₁ y₁ y₂) (tm₁ y₁ y₂) (tp₂ y₁ y₂) (tm₂ y₁ y₂) with hM
  set PU := ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwU q a (π₁ y₁) (π₂ y₂) S₁ f₁ l₁ (tp₁ y₁ y₂) (tm₁ y₁ y₂) with hPU
  set PL := ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwL q a (π₁ y₁) (π₂ y₂) S₂ f₂ l₂ (tp₂ y₁ y₂) (tm₂ y₁ y₂) with hPL
  have hpt := fun y₁ (hy₁ : y₁ ∈ Y₁) y₂ (hy₂ : y₂ ∈ Y₂) =>
    leaf_two_sided (q := q) a N₁ N₂ hN (π₁ y₁) (π₂ y₂) (hπ₁ y₁ hy₁) (hπ₂ y₂ hy₂) R S₁ f₁ l₁ hf₁ hR₁ S₂ f₂ l₂ hf₂ hR₂
      (tp₁ y₁ y₂) (tm₁ y₁ y₂) (tp₂ y₁ y₂) (tm₂ y₁ y₂) (hℓ₁ y₁ hy₁ y₂ hy₂) (hℓ₂ y₁ hy₁ y₂ hy₂)
      (hsp₁ y₁ hy₁ y₂ hy₂) (hsp₂ y₁ hy₁ y₂ hy₂)
  have hU : X ≤ M + PU := by
    rw [hX, hM, hPU, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y₁ hy₁ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y₂ hy₂ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hpt y₁ hy₁ y₂ hy₂).1 (hc y₁ hy₁ y₂ hy₂)
  have hL : -M + PL ≤ X := by
    rw [hX, hM, hPL, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y₁ hy₁ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y₂ hy₂ => ?_
    rw [← mul_neg, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hpt y₁ hy₁ y₂ hy₂).2 (hc y₁ hy₁ y₂ hy₂)
  rw [abs_le]
  constructor
  · have := neg_abs_le PL
    have := abs_nonneg PU
    linarith
  · have := le_abs_self PU
    have := abs_nonneg PL
    linarith

/-! ### The bilinear parts, by pairs of blocks -/

omit [NeZero q] in
/-- A spline's sum of `dw` is real: `ssum(t, dw, d)` as a complex number is `Σ_k w(k)dw(dk)`. -/
theorem ssum_dwR_eq (a : ZMod q) (t : ℕ × ℕ × ℕ × ℕ) (d : ℕ) :
    ((ssum t (dwR q a) d : ℝ) : ℂ) = ∑ k ∈ suppv t, ((splv t k : ℝ) : ℂ) * SieveFamily.dw q a (d * k) := by
  unfold ssum
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dw_eq]
  rfl

omit [NeZero q] in
/-- **Regrouping by pairs of blocks.** If `b₁` maps `Y₁ × S` into `B₁` and `b₂` maps `Y₂` into `B₂`, then
`Σ_{y₁,y₂,σ} F = Σ_{β₁∈B₁} Σ_{β₂∈B₂} Σ_{(y₁,σ): b₁ = β₁} Σ_{y₂: b₂ = β₂} F`. -/
theorem sum_blocks {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (S : Finset κ) (B₁ B₂ : Finset ℕ)
    (b₁ : ι₁ × κ → ℕ) (b₂ : ι₂ → ℕ) (hb₁ : ∀ x ∈ Y₁ ×ˢ S, b₁ x ∈ B₁) (hb₂ : ∀ y ∈ Y₂, b₂ y ∈ B₂)
    (F : ι₁ → ι₂ → κ → ℝ) :
    ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, ∑ σ ∈ S, F y₁ y₂ σ =
      ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂, ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ x = β₁),
        ∑ y₂ ∈ Y₂.filter (fun y => b₂ y = β₂), F x.1 y₂ x.2 := by
  classical
  have h1 : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, ∑ σ ∈ S, F y₁ y₂ σ = ∑ x ∈ Y₁ ×ˢ S, ∑ y₂ ∈ Y₂, F x.1 y₂ x.2 := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun y₁ _ => Finset.sum_comm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hb₁]
  refine Finset.sum_congr rfl fun β₁ _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_fiberwise_of_maps_to hb₂]
  refine Finset.sum_congr rfl fun β₂ _ => ?_
  exact Finset.sum_comm

/-- A block pair's bilinear sum: over `(y₁, σ)` with `b₁(π₁(y₁)f_σ) = β₁` and `y₂` with `b₂(π₂(y₂)) = β₂`, of
`λ(σ)c(y₁, y₂)Σ_k w_t(k)dw(π₁(y₁)f_σπ₂(y₂)k)`, in the form of `SieveTypeIBFam.typeIB_sharp0`. -/
noncomputable def blockSum (q : ℕ) (a : ZMod q) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ)
    (π₂ : ι₂ → ℕ) (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (c : ι₁ → ι₂ → ℝ) (b₁ b₂ : ℕ → ℕ) (β₁ β₂ : ℕ)
    (t : ℕ × ℕ × ℕ × ℕ) : ℂ :=
  ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ (π₁ x.1 * f x.2) = β₁), ∑ y₂ ∈ Y₂.filter (fun y => b₂ (π₂ y) = β₂),
    ((lam x.2 : ℝ) : ℂ) * (1 : ℂ) * ((c x.1 y₂ : ℝ) : ℂ) *
      ∑ k ∈ suppv t, ((splv t k : ℝ) : ℂ) * SieveFamily.dw q a (π₁ x.1 * f x.2 * π₂ y₂ * k)

omit [NeZero q] in
/-- The real sum of a block pair is its `blockSum`. -/
theorem block_real (a : ZMod q) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (c : ι₁ → ι₂ → ℝ) (b₁ b₂ : ℕ → ℕ) (β₁ β₂ : ℕ)
    (t : ℕ × ℕ × ℕ × ℕ) :
    ((∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ (π₁ x.1 * f x.2) = β₁), ∑ y₂ ∈ Y₂.filter (fun y => b₂ (π₂ y) = β₂),
        c x.1 y₂ * (lam x.2 * ssum t (dwR q a) (π₁ x.1 * f x.2 * π₂ y₂)) : ℝ) : ℂ) =
      blockSum q a Y₁ Y₂ π₁ π₂ S f lam c b₁ b₂ β₁ β₂ t := by
  rw [blockSum]
  push_cast
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y₂ _ => ?_
  rw [ssum_dwR_eq]
  ring

omit [NeZero q] in
/-- **The bilinear part above, by block pairs.** With the splines `TP(β₁, β₂)`, `TM(β₁, β₂)` of the block pair of
`(π₁(y₁)f_σ, π₂(y₂))`, `|Σ_y c·dwU|` is at most `Σ_{β₁,β₂} (|blockSum(λ₊, TP)| + |blockSum(λ₋, TM)|)`. -/
theorem abs_dwU_le (a : ZMod q) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (c : ι₁ → ι₂ → ℝ) (b₁ b₂ : ℕ → ℕ) (B₁ B₂ : Finset ℕ)
    (hb₁ : ∀ x ∈ Y₁ ×ˢ S, b₁ (π₁ x.1 * f x.2) ∈ B₁) (hb₂ : ∀ y ∈ Y₂, b₂ (π₂ y) ∈ B₂)
    (TP TM : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) :
    |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwU q a (π₁ y₁) (π₂ y₂) S f lam
        (fun σ => TP (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (fun σ => TM (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂)))| ≤
      ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂,
        (‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => ppart (lam σ)) c b₁ b₂ β₁ β₂ (TP β₁ β₂)‖ +
          ‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => npart (lam σ)) c b₁ b₂ β₁ β₂ (TM β₁ β₂)‖) := by
  classical
  set F : ι₁ → ι₂ → κ → ℝ := fun y₁ y₂ σ =>
    c y₁ y₂ * (ppart (lam σ) * ssum (TP (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (dwR q a) (π₁ y₁ * f σ * π₂ y₂)) -
      c y₁ y₂ * (npart (lam σ) * ssum (TM (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (dwR q a) (π₁ y₁ * f σ * π₂ y₂))
    with hF
  have e1 : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwU q a (π₁ y₁) (π₂ y₂) S f lam
      (fun σ => TP (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (fun σ => TM (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) =
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, ∑ σ ∈ S, F y₁ y₂ σ := by
    refine Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [dwU, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [hF]; ring
  rw [e1, sum_blocks Y₁ Y₂ S B₁ B₂ (fun x => b₁ (π₁ x.1 * f x.2)) (fun y => b₂ (π₂ y)) hb₁ hb₂ F]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β₁ _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β₂ _ => ?_)
  -- inside the block pair the splines are `TP β₁ β₂` and `TM β₁ β₂`
  have e2 : ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ (π₁ x.1 * f x.2) = β₁),
        ∑ y₂ ∈ Y₂.filter (fun y => b₂ (π₂ y) = β₂), F x.1 y₂ x.2 =
      (∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ (π₁ x.1 * f x.2) = β₁), ∑ y₂ ∈ Y₂.filter (fun y => b₂ (π₂ y) = β₂),
        c x.1 y₂ * (ppart (lam x.2) * ssum (TP β₁ β₂) (dwR q a) (π₁ x.1 * f x.2 * π₂ y₂))) -
      ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => b₁ (π₁ x.1 * f x.2) = β₁), ∑ y₂ ∈ Y₂.filter (fun y => b₂ (π₂ y) = β₂),
        c x.1 y₂ * (npart (lam x.2) * ssum (TM β₁ β₂) (dwR q a) (π₁ x.1 * f x.2 * π₂ y₂)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y₂ hy₂ => ?_
    simp only [hF]
    rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy₂).2]
  rw [e2]
  refine (abs_sub _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · rw [← block_real a Y₁ Y₂ π₁ π₂ S f (fun σ => ppart (lam σ)) c b₁ b₂ β₁ β₂ (TP β₁ β₂), Complex.norm_real,
      Real.norm_eq_abs]
  · rw [← block_real a Y₁ Y₂ π₁ π₂ S f (fun σ => npart (lam σ)) c b₁ b₂ β₁ β₂ (TM β₁ β₂), Complex.norm_real,
      Real.norm_eq_abs]

omit [NeZero q] in
/-- **The bilinear part below, by block pairs**: the same for `dwL`, whose splines enter as `λ₊TM − λ₋TP`. -/
theorem abs_dwL_le (a : ZMod q) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (c : ι₁ → ι₂ → ℝ) (b₁ b₂ : ℕ → ℕ) (B₁ B₂ : Finset ℕ)
    (hb₁ : ∀ x ∈ Y₁ ×ˢ S, b₁ (π₁ x.1 * f x.2) ∈ B₁) (hb₂ : ∀ y ∈ Y₂, b₂ (π₂ y) ∈ B₂)
    (TP TM : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) :
    |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, c y₁ y₂ * dwL q a (π₁ y₁) (π₂ y₂) S f lam
        (fun σ => TP (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (fun σ => TM (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂)))| ≤
      ∑ β₁ ∈ B₁, ∑ β₂ ∈ B₂,
        (‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => ppart (lam σ)) c b₁ b₂ β₁ β₂ (TM β₁ β₂)‖ +
          ‖blockSum q a Y₁ Y₂ π₁ π₂ S f (fun σ => npart (lam σ)) c b₁ b₂ β₁ β₂ (TP β₁ β₂)‖) := by
  have h := abs_dwU_le (q := q) a Y₁ Y₂ π₁ π₂ S f lam c b₁ b₂ B₁ B₂ hb₁ hb₂ TM TP
  have e : ∀ y₁ y₂, dwL q a (π₁ y₁) (π₂ y₂) S f lam
      (fun σ => TP (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (fun σ => TM (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) =
      dwU q a (π₁ y₁) (π₂ y₂) S f lam
        (fun σ => TM (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) (fun σ => TP (b₁ (π₁ y₁ * f σ)) (b₂ (π₂ y₂))) := by
    intro y₁ y₂; rfl
  simp only [e]
  exact h

end SieveTypeIBLeaf
