/-
# Weights for the bilinear Type I estimate: Parseval for the weight, intervals and splines

Plain statements, with `e(x) = e^{2πix/q}` (`SieveTypeIB.eq`), `ŵ(h) = Σ_{k∈S} w(k)e(hk)` (`SieveTypeIB.what`) and
`E_w = Σ_{k∈S} w(k)1[(k, q) = 1] − (φ(q)/q)Σ_{k∈S} w(k)` (`SieveTypeIB.Ew`).

* `sum_norm_what_sq_le`: if each residue class holds at most `M` elements of `S`, `Σ_h |ŵ(h)|² ≤ qMΣ_{k∈S}|w(k)|²`.
* `norm_sum_range_le`, `norm_sum_Ioc_le`: for an integer `t` with `0 < |t|` and `2|t| ≤ q`,
  `|Σ_{i<Y} e(t(u + i))| ≤ q/(2|t|)` and `|Σ_{A<k≤B} e(tk)| ≤ q/(2|t|)`.
* `spl`, the spline `w(k) = ℓ^{−r}#{(i, j) : A < i ≤ B, j ∈ [0, ℓ)^r, i + Σj = k}` (`ℓ ≥ 1`), an average of the
  indicators of the intervals `(A + Σj, B + Σj]` (`sum_spl_mul`), of mass `B − A` (`sum_spl`): `spl_nonneg`,
  `spl_le_one` and `spl_eq_one`
  (`0 ≤ w ≤ 1`, and `w = 1` on `(A + r(ℓ − 1), B]`), `spl_eq_zero` (`w = 0` off `supp = (A, B + r(ℓ − 1)]`),
  `what_spl` (`ŵ(h) = ℓ^{−r}(Σ_{A<i≤B} e(hi))(Σ_{j<ℓ} e(hj))^r`), `norm_what_spl_le` (for `0 < |t|`, `2|t| ≤ q`:
  `|ŵ(t)| ≤ (B − A)(q/(2ℓ|t|))^r`) and `norm_what_spl_tail` (for `h ≠ 0` off the image of `[−H, H]`:
  `|ŵ(h)| ≤ (B − A)(q/(2ℓ(H + 1)))^r`).
* `norm_Ew_Ioc_le`, `norm_Ew_spl_le`: `|E_w| ≤ d(q)` for the indicator of an interval and for a spline.
* `typeIB_spline`: `SieveTypeIB.typeIB_bound` with a spline weight on its support. For `D₁`, `D₂` prime to `q` with
  `D₂ ⊆ [1, Dm]`, `2HDm < q`, every residue the inverse of at most `m` elements of `D₁` and every `|t|d`
  (`0 < |t| ≤ H`, `d ∈ D₂`) with at most `F` divisors, `|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_k w(k)dw(d₁d₂k)|` is at most
  `(Σ|α|²)^{1/2}(mF(Σ|β|²)(⌊n/q⌋ + 1)n)^{1/2} + (B − A)(q/(2ℓ(H + 1)))^r(Σ|α|)(Σ|β|) + |Σα||Σβ|d(q)/φ(q)`, where
  `n = B + r(ℓ − 1) − A` is the length of the support.

The proof:

* `sum_norm_what_sq_le`: `SieveTypeIB.sum_norm_sq_le`, and `|w_k||w_k′| ≤ ½(|w_k|² + |w_k′|²)` over the pairs in a
  residue class.
* `norm_sum_range_le`: `ExpSum.geom_bound` at `θ = t/q`, whose distance to the nearest integer is `|t|/q`.
* `what_spl`: `sum_spl_mul` (the spline's tuples, fibred by their sum), `e(i + Σj) = e(i)∏_m e(j_m)` and
  `Finset.prod_univ_sum`; `norm_what_spl_le`: the interval's sum is at most `B − A` in size, and
  `norm_sum_range_le` bounds each of the `r` factors.
* `norm_what_spl_tail`: `h = t` with `t` its least absolute residue (`ZMod.valMinAbs`), so `2|t| ≤ q`, and `|t| > H`.
* `norm_sum_Ioc_unit_le`: by Möbius over the divisors of `q` (`ind_unit_eq`, `totient_div_eq`), the sum is
  `Σ_{d|q} μ(d)((⌊D/d⌋ − ⌊C/d⌋) − (D − C)/d)`, and each bracket is `((C mod d) − (D mod d))/d`, of size below `1`.
  The spline's `E_w` averages the intervals' (`sum_spl_mul`).
* `typeIB_spline`: `card_Ioc_filter_cong_le` gives `M = ⌊n/q⌋ + 1` in `sum_norm_what_sq_le`, and `|w| ≤ 1`.

The file imports `SieveTypeIB.lean` and `ExpSum.lean` (for the geometric sum).
-/
import SieveTypeIB
import ExpSum

open Finset Complex

namespace SieveSpline

open SieveTypeIB

variable {q : ℕ} [NeZero q]

/-! ### Parseval for the weight -/

/-- **Parseval for the weight**: if each residue class holds at most `M` elements of `S`,
`Σ_h |ŵ(h)|² ≤ qMΣ_{k∈S}|w(k)|²`. -/
theorem sum_norm_what_sq_le (S : Finset ℕ) (w : ℕ → ℂ) {M : ℕ}
    (hM : ∀ k ∈ S, #(S.filter (fun k' : ℕ => (k' : ZMod q) = (k : ZMod q))) ≤ M) :
    ∑ h : ZMod q, ‖what S w h‖ ^ 2 ≤ q * (M * ∑ k ∈ S, ‖w k‖ ^ 2) := by
  have h1 := sum_norm_sq_le S w (fun k => (k : ZMod q))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg q))
  -- `|w_k||w_k′| ≤ ½(|w_k|² + |w_k′|²)`, and the relation is symmetric
  have hterm : ∀ k ∈ S, ∀ k' ∈ S, (if (k : ZMod q) = k' then ‖w k‖ * ‖w k'‖ else 0) ≤
      (if (k : ZMod q) = k' then ‖w k‖ ^ 2 / 2 else 0) + (if (k : ZMod q) = k' then ‖w k'‖ ^ 2 / 2 else 0) := by
    intro k _ k' _
    split_ifs
    · nlinarith [sq_nonneg (‖w k‖ - ‖w k'‖)]
    · simp
  have hsym : ∑ k ∈ S, ∑ k' ∈ S, (if (k : ZMod q) = k' then ‖w k'‖ ^ 2 / 2 else 0) =
      ∑ k ∈ S, ∑ k' ∈ S, (if (k : ZMod q) = k' then ‖w k‖ ^ 2 / 2 else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ =>
      if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl
  calc ∑ k ∈ S, ∑ k' ∈ S, (if (k : ZMod q) = k' then ‖w k‖ * ‖w k'‖ else 0)
      ≤ ∑ k ∈ S, ∑ k' ∈ S, ((if (k : ZMod q) = k' then ‖w k‖ ^ 2 / 2 else 0) +
          (if (k : ZMod q) = k' then ‖w k'‖ ^ 2 / 2 else 0)) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun k' hk' => hterm k hk k' hk'
    _ = ∑ k ∈ S, ‖w k‖ ^ 2 * #(S.filter (fun k' : ℕ => (k' : ZMod q) = (k : ZMod q))) := by
        simp only [Finset.sum_add_distrib]
        rw [hsym, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have e : ∀ x ∈ S, ((if (k : ZMod q) = x then ‖w k‖ ^ 2 / 2 else 0) +
            (if (k : ZMod q) = x then ‖w k‖ ^ 2 / 2 else 0)) =
            (if (x : ZMod q) = (k : ZMod q) then ‖w k‖ ^ 2 else 0) := by
          intro x _
          by_cases h : (k : ZMod q) = x
          · rw [ite_eq_left h, ite_eq_left h.symm]; ring
          · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]; ring
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl e, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ k ∈ S, ‖w k‖ ^ 2 * M :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (by exact_mod_cast hM k hk) (by positivity)
    _ = M * ∑ k ∈ S, ‖w k‖ ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The interval's transform -/

/-- `e(t) = e^{2πit/q}` for an integer `t`, as `ExpSum`'s `ee`. -/
theorem eq_intCast (t : ℤ) : eq ((t : ZMod q)) = Vinogradov.ee ((t : ℝ) / q) := by
  rw [eq, ZMod.stdAddChar_coe, Vinogradov.ee]
  congr 1
  push_cast
  ring

/-- For `|θ| ≤ 1/2`, the distance of `θ` to the nearest integer is `|θ|`. -/
theorem abs_sub_round_of_abs_le {θ : ℝ} (h : |θ| ≤ 1 / 2) : |θ - round θ| = |θ| := by
  rcases eq_or_lt_of_le h with h2 | h2
  · -- `|θ| = 1/2`
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.1 h2 with h3 | h3
    · have : round θ = 1 := by
        rw [round_eq, h3, show (1 / 2 : ℝ) + 1 / 2 = (1 : ℤ) by norm_num, Int.floor_intCast]
      rw [this, h3]; norm_num
    · have : round θ = 0 := round_eq_zero_iff.2 ⟨by rw [h3], by rw [h3]; norm_num⟩
      rw [this, Int.cast_zero, sub_zero]
  · have : round θ = 0 := round_eq_zero_iff.2 ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
    rw [this, Int.cast_zero, sub_zero]

/-- **The geometric sum**: for an integer `t ≠ 0` with `2|t| ≤ q`, `|Σ_{i<Y} e(t(u + i))| ≤ q/(2|t|)`. -/
theorem norm_sum_range_le (u Y : ℕ) {t : ℤ} (ht : t ≠ 0) (htq : 2 * |t| ≤ q) :
    ‖∑ i ∈ range Y, eq ((t : ZMod q) * ((u + i : ℕ) : ZMod q))‖ ≤ q / (2 * |t|) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have htR : (0 : ℝ) < |(t : ℝ)| := by rw [abs_pos]; exact_mod_cast ht
  set θ : ℝ := (t : ℝ) / q with hθ
  have hθ2 : |θ| ≤ 1 / 2 := by
    rw [hθ, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    have : (2 * |t| : ℝ) ≤ q := by exact_mod_cast htq
    rw [← Int.cast_abs] at *; linarith
  have hround := abs_sub_round_of_abs_le hθ2
  have hθ0 : θ - round θ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hround
    have : |θ| > 0 := by rw [hθ, abs_div, abs_of_pos hq0]; exact div_pos htR hq0
    linarith
  -- the terms as `ee(θ(u + i))`
  have hsum : ∑ i ∈ range Y, eq ((t : ZMod q) * ((u + i : ℕ) : ZMod q)) =
      ∑ i ∈ range Y, Vinogradov.ee (θ * ((u : ℝ) + i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((t : ZMod q) * ((u + i : ℕ) : ZMod q)) = (((t * (u + i : ℕ) : ℤ)) : ZMod q) by push_cast; ring,
      eq_intCast, hθ]
    congr 1
    push_cast
    ring
  rw [hsum]
  refine (ExpSum.geom_bound θ _ Y hθ0).trans ?_
  rw [hround, hθ, abs_div, abs_of_pos hq0]
  rw [show (1 : ℝ) / (2 * (|(t : ℝ)| / q)) = q / (2 * |(t : ℝ)|) by field_simp]
  rw [Int.cast_abs]

/-! ### Splines -/

/-- `e(Σ_m f(m)) = Π_m e(f(m))`. -/
theorem eq_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod q) : eq (∑ m ∈ s, f m) = ∏ m ∈ s, eq (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, eq_add, ih]

/-- The tuples `(i, j)` with `A < i ≤ B` and `j ∈ [0, ℓ)^r`. -/
def tup (A B ℓ r : ℕ) : Finset (ℕ × (Fin r → ℕ)) := Ioc A B ×ˢ Fintype.piFinset (fun _ : Fin r => range ℓ)

/-- The sum `i + Σ_m j_m` of a tuple. -/
def tsum {r : ℕ} (x : ℕ × (Fin r → ℕ)) : ℕ := x.1 + ∑ m, x.2 m

/-- **The spline** `w(k) = ℓ^{−r}#{(i, j) : A < i ≤ B, j ∈ [0, ℓ)^r, i + Σj = k}`. -/
noncomputable def spl (A B ℓ r k : ℕ) : ℝ := (#((tup A B ℓ r).filter (fun x => tsum x = k)) : ℝ) / (ℓ : ℝ) ^ r

/-- The spline's support, `(A, B + r(ℓ − 1)]`. -/
def supp (A B ℓ r : ℕ) : Finset ℕ := Ioc A (B + r * (ℓ - 1))

theorem sum_le_of_mem {r ℓ : ℕ} {j : Fin r → ℕ} (hj : j ∈ Fintype.piFinset (fun _ : Fin r => range ℓ)) :
    ∑ m, j m ≤ r * (ℓ - 1) := by
  have : ∀ m, j m ≤ ℓ - 1 := fun m => by
    have := Fintype.mem_piFinset.1 hj m
    rw [Finset.mem_range] at this; omega
  calc ∑ m, j m ≤ ∑ _m : Fin r, (ℓ - 1) := Finset.sum_le_sum fun m _ => this m
    _ = r * (ℓ - 1) := by simp

theorem tsum_mem_supp {A B ℓ r : ℕ} {x : ℕ × (Fin r → ℕ)} (hx : x ∈ tup A B ℓ r) : tsum x ∈ supp A B ℓ r := by
  rw [tup, Finset.mem_product, Finset.mem_Ioc] at hx
  have := sum_le_of_mem hx.2
  rw [supp, Finset.mem_Ioc, tsum]
  omega

/-- **The spline as an average** of the intervals `(A + Σj, B + Σj]`: for `ℓ ≥ 1`,
`Σ_{k∈supp} w(k)f(k) = ℓ^{−r}Σ_{(i,j)} f(i + Σj)`. -/
theorem sum_spl_mul (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (f : ℕ → ℂ) :
    ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * f k = ((ℓ : ℂ) ^ r)⁻¹ * ∑ x ∈ tup A B ℓ r, f (tsum x) := by
  have hℓ0 : (ℓ : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : ℓ ≠ 0))
  rw [← Finset.sum_fiberwise_of_maps_to (g := tsum) (t := supp A B ℓ r) (fun x hx => tsum_mem_supp hx),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const, nsmul_eq_mul, spl]
  push_cast
  field_simp

theorem spl_nonneg (A B ℓ r k : ℕ) : 0 ≤ spl A B ℓ r k := by unfold spl; positivity

/-- The spline's mass: `Σ_k w(k) = B − A`. -/
theorem sum_spl (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) : ∑ k ∈ supp A B ℓ r, spl A B ℓ r k = ((B - A : ℕ) : ℝ) := by
  have h := sum_spl_mul A B ℓ r hℓ (fun _ => 1)
  have hℓ0 : (ℓ : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : ℓ ≠ 0))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  rw [tup, Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
    Fintype.card_fin, Nat.card_Ioc] at h
  push_cast at h
  rw [mul_comm ((B - A : ℕ) : ℂ), ← mul_assoc, inv_mul_cancel₀ hℓ0, one_mul] at h
  exact_mod_cast h

/-- `w ≤ 1`: a tuple summing to `k` is fixed by its `j`. -/
theorem spl_le_one (A B ℓ r k : ℕ) (hℓ : 1 ≤ ℓ) : spl A B ℓ r k ≤ 1 := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) ^ r := by positivity
  rw [spl, div_le_one hℓ0]
  have hcard : #((tup A B ℓ r).filter (fun x => tsum x = k)) ≤ ℓ ^ r := by
    calc #((tup A B ℓ r).filter (fun x => tsum x = k))
        ≤ #(Fintype.piFinset (fun _ : Fin r => range ℓ)) := by
          refine Finset.card_le_card_of_injOn (fun x => x.2) ?_ ?_
          · intro x hx
            simp only [Finset.coe_filter, tup, Finset.mem_product, Set.mem_ofPred_eq] at hx
            exact hx.1.2
          · intro x hx y hy hxy
            simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
            simp only at hxy
            have h1 : x.1 = y.1 := by
              have := hx.2; have := hy.2; unfold tsum at *; rw [hxy] at *; omega
            exact Prod.ext h1 hxy
      _ = ℓ ^ r := by simp
  exact_mod_cast hcard

/-- `w = 1` on `(A + r(ℓ − 1), B]`. -/
theorem spl_eq_one (A B ℓ r k : ℕ) (hℓ : 1 ≤ ℓ) (hk1 : A + r * (ℓ - 1) < k) (hk2 : k ≤ B) :
    spl A B ℓ r k = 1 := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) ^ r := by positivity
  rw [spl, div_eq_one_iff_eq hℓ0.ne']
  have hcard : #((tup A B ℓ r).filter (fun x => tsum x = k)) = ℓ ^ r := by
    have h := Finset.card_nbij' (s := (tup A B ℓ r).filter (fun x => tsum x = k))
      (t := Fintype.piFinset (fun _ : Fin r => range ℓ)) (fun x => x.2) (fun j => (k - ∑ m, j m, j)) ?_ ?_ ?_ ?_
    · rw [h]; simp
    · intro x hx
      simp only [Finset.coe_filter, tup, Finset.mem_product, Set.mem_ofPred_eq] at hx
      exact hx.1.2
    · intro j hj
      have hj' : j ∈ Fintype.piFinset (fun _ : Fin r => range ℓ) := hj
      have := sum_le_of_mem hj'
      simp only [Finset.mem_coe]
      rw [Finset.mem_filter, tup, Finset.mem_product, Finset.mem_Ioc]
      dsimp only
      refine ⟨⟨⟨by omega, by omega⟩, hj'⟩, ?_⟩
      show k - ∑ m, j m + ∑ m, j m = k
      omega
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
      have h2 := hx.2
      unfold tsum at h2
      exact Prod.ext (by simp only; omega) rfl
    · intro j _
      rfl
  exact_mod_cast hcard

/-- `w = 0` off the support. -/
theorem spl_eq_zero (A B ℓ r k : ℕ) (hk : k ∉ supp A B ℓ r) : spl A B ℓ r k = 0 := by
  rw [spl, div_eq_zero_iff]
  left
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx h
  exact hk (h ▸ tsum_mem_supp hx)

/-- **The spline's transform**: `ŵ(h) = ℓ^{−r}(Σ_{A<i≤B} e(hi))(Σ_{j<ℓ} e(hj))^r`. -/
theorem what_spl (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (h : ZMod q) :
    what (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ)) h =
      ((ℓ : ℂ) ^ r)⁻¹ * ((∑ i ∈ Ioc A B, eq (h * (i : ZMod q))) * (∑ j ∈ range ℓ, eq (h * (j : ZMod q))) ^ r) := by
  rw [what, sum_spl_mul A B ℓ r hℓ (fun k => eq (h * (k : ZMod q)))]
  congr 1
  rw [tup, Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpow : (∑ j ∈ range ℓ, eq (h * (j : ZMod q))) ^ r =
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => range ℓ), ∏ m, eq (h * ((j m : ℕ) : ZMod q)) := by
    rw [← Finset.prod_univ_sum (fun _ : Fin r => range ℓ) (fun _ j => eq (h * (j : ZMod q))),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum]
  simp only
  push_cast
  rw [mul_add, eq_add, Finset.mul_sum, eq_sum]

/-- **The spline's decay**: for an integer `t ≠ 0` with `2|t| ≤ q`, `|ŵ(t)| ≤ (B − A)(q/(2ℓ|t|))^r`. -/
theorem norm_what_spl_le (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {t : ℤ} (ht : t ≠ 0) (htq : 2 * |t| ≤ q) :
    ‖what (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ)) (t : ZMod q)‖ ≤
      ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * |(t : ℝ)|)) ^ r := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have htR : (0 : ℝ) < |(t : ℝ)| := by rw [abs_pos]; exact_mod_cast ht
  rw [what_spl A B ℓ r hℓ, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, norm_mul, norm_pow]
  have hI : ‖∑ i ∈ Ioc A B, eq ((t : ZMod q) * (i : ZMod q))‖ ≤ ((B - A : ℕ) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_eq, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc, le_refl]
  have hJ : ‖∑ j ∈ range ℓ, eq ((t : ZMod q) * (j : ZMod q))‖ ≤ q / (2 * |(t : ℝ)|) := by
    have := norm_sum_range_le (q := q) 0 ℓ ht htq
    simpa [Int.cast_abs] using this
  calc ((ℓ : ℝ) ^ r)⁻¹ * (‖∑ i ∈ Ioc A B, eq ((t : ZMod q) * (i : ZMod q))‖ *
        ‖∑ j ∈ range ℓ, eq ((t : ZMod q) * (j : ZMod q))‖ ^ r)
      ≤ ((ℓ : ℝ) ^ r)⁻¹ * (((B - A : ℕ) : ℝ) * (q / (2 * |(t : ℝ)|)) ^ r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hI (pow_le_pow_left₀ (norm_nonneg _) hJ r)
          (by positivity) (by positivity)) (by positivity)
    _ = ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * |(t : ℝ)|)) ^ r := by
        rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow]
        field_simp

/-- **The spline's tail**: for `h ≠ 0` outside the image of `[−H, H]`, `|ŵ(h)| ≤ (B − A)(q/(2ℓ(H + 1)))^r`. -/
theorem norm_what_spl_tail (A B ℓ r H : ℕ) (hℓ : 1 ≤ ℓ) (h : ZMod q) (h0 : h ≠ 0)
    (hH : h ∉ (Jset H).image (fun t : ℤ => (t : ZMod q))) :
    ‖what (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ)) h‖ ≤
      ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r := by
  have hth : ((h.valMinAbs : ℤ) : ZMod q) = h := ZMod.coe_valMinAbs h
  have ht0 : h.valMinAbs ≠ 0 := by rwa [Ne, ZMod.valMinAbs_eq_zero]
  have hle := ZMod.natAbs_valMinAbs_le h
  have htq : 2 * |h.valMinAbs| ≤ q := by
    have : 2 * h.valMinAbs.natAbs ≤ q := by omega
    rw [Int.abs_eq_natAbs]; exact_mod_cast this
  have htH : H + 1 ≤ h.valMinAbs.natAbs := by
    by_contra hlt
    exact hH (Finset.mem_image.2 ⟨h.valMinAbs, mem_Jset.2 ⟨ht0, by omega⟩, hth⟩)
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  rw [← hth]
  refine (norm_what_spl_le A B ℓ r hℓ ht0 htq).trans ?_
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ r) (by positivity)
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have : ((H : ℝ) + 1) ≤ |((h.valMinAbs : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast htH
  nlinarith

/-! ### The weight's mean on the units, by Möbius -/

/-- `Σ_{d|n} μ(d) = [n = 1]`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at h
  exact h

/-- `1[(k, q) = 1] = Σ_{d|q, d|k} μ(d)`. -/
theorem ind_unit_eq (k : ℕ) : (if IsUnit (k : ZMod q) then (1 : ℂ) else 0) =
    ∑ d ∈ q.divisors, if d ∣ k then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
  have hq : q ≠ 0 := NeZero.ne q
  have hg : k.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
  have hdiv : q.divisors.filter (fun d => d ∣ k) = (k.gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, h1⟩, hg⟩
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hq⟩, h1⟩
  rw [← Finset.sum_filter, hdiv, sum_divisors_moebius]
  by_cases hu : IsUnit (k : ZMod q)
  · rw [ite_eq_left hu, ite_eq_left ((ZMod.isUnit_iff_coprime k q).1 hu)]
  · rw [ite_eq_right hu, ite_eq_right (fun h => hu ((ZMod.isUnit_iff_coprime k q).2 h))]

/-- `φ(q)/q = Σ_{d|q} μ(d)/d`. -/
theorem totient_div_eq : (q.totient : ℂ) / q = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) / d := by
  have hq : 0 < q := NeZero.pos q
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ) (f := fun n => (n.totient : ℂ))
    (g := fun n => (n : ℂ))).1 (fun n _ => by exact_mod_cast Nat.sum_totient n) q hq
  rw [Nat.sum_divisorsAntidiagonal (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℂ) * (b : ℂ))] at h
  rw [← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdq hd0]
  field_simp

/-- `#{k ∈ (C, D] : d | k} = ⌊D/d⌋ − ⌊C/d⌋`. -/
theorem card_Ioc_filter_dvd (C D d : ℕ) (hCD : C ≤ D) : #((Ioc C D).filter (d ∣ ·)) = D / d - C / d := by
  have h1 : (Ioc 0 D).filter (d ∣ ·) = (Ioc 0 C).filter (d ∣ ·) ∪ (Ioc C D).filter (d ∣ ·) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le C) hCD]
  have h2 : Disjoint ((Ioc 0 C).filter (d ∣ ·)) ((Ioc C D).filter (d ∣ ·)) :=
    Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)
  have h3 := Finset.card_union_of_disjoint h2
  rw [← h1, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at h3
  omega

/-- The weight on the units less its mean, termwise: `E_w = Σ_{k∈S} w(k)(1[(k, q) = 1] − φ(q)/q)`. -/
theorem Ew_eq (S : Finset ℕ) (w : ℕ → ℂ) :
    Ew (q := q) S w = ∑ k ∈ S, w k * ((if IsUnit (k : ZMod q) then 1 else 0) - (q.totient : ℂ) / q) := by
  rw [Ew, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The units in an interval**: `|Σ_{C<k≤D}(1[(k, q) = 1] − φ(q)/q)| ≤ d(q)`. -/
theorem norm_sum_Ioc_unit_le (C D : ℕ) :
    ‖∑ k ∈ Ioc C D, ((if IsUnit (k : ZMod q) then (1 : ℂ) else 0) - (q.totient : ℂ) / q)‖ ≤ q.divisors.card := by
  rcases lt_or_ge D C with hDC | hCD
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]; positivity
  -- Möbius: the sum is `Σ_{d|q} μ(d)((⌊D/d⌋ − ⌊C/d⌋) − (D − C)/d)`
  have hsum : ∑ k ∈ Ioc C D, ((if IsUnit (k : ZMod q) then (1 : ℂ) else 0) - (q.totient : ℂ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (((D / d - C / d : ℕ) : ℂ) - ((D : ℂ) - C) / d) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, totient_div_eq]
    simp only [ind_unit_eq]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_Ioc_filter_dvd C D d hCD, Nat.cast_sub hCD]
    ring
  rw [hsum]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun d hd => ?_).trans (by simp))
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [norm_mul]
  have hμ : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  -- `⌊D/d⌋ − ⌊C/d⌋ − (D − C)/d = (C mod d − D mod d)/d`
  have hfrac : (((D / d - C / d : ℕ) : ℂ) - ((D : ℂ) - C) / d) = ((((C % d : ℕ) : ℝ) - (D % d : ℕ)) / d : ℝ) := by
    have hle : C / d ≤ D / d := Nat.div_le_div_right hCD
    have e1 := Nat.div_add_mod D d
    have e2 := Nat.div_add_mod C d
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
    have e1' : (d : ℂ) * ((D / d : ℕ) : ℂ) + ((D % d : ℕ) : ℂ) = D := by exact_mod_cast e1
    have e2' : (d : ℂ) * ((C / d : ℕ) : ℂ) + ((C % d : ℕ) : ℂ) = C := by exact_mod_cast e2
    linear_combination e1' - e2'
  have hb : ‖(((D / d - C / d : ℕ) : ℂ) - ((D : ℂ) - C) / d)‖ ≤ 1 := by
    rw [hfrac, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hdR, div_le_one hdR]
    have h1 : C % d < d := Nat.mod_lt C hd0
    have h2 : D % d < d := Nat.mod_lt D hd0
    rw [abs_le]
    constructor
    · have : ((D % d : ℕ) : ℝ) < d := by exact_mod_cast h2
      have : (0 : ℝ) ≤ ((C % d : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have : ((C % d : ℕ) : ℝ) < d := by exact_mod_cast h1
      have : (0 : ℝ) ≤ ((D % d : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖(((D / d - C / d : ℕ) : ℂ) - ((D : ℂ) - C) / d)‖
      ≤ 1 * 1 := mul_le_mul hμ hb (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **`E_w` for a spline**: `|E_w| ≤ d(q)`, as the spline averages the indicators of intervals. -/
theorem norm_Ew_spl_le (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) :
    ‖Ew (q := q) (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ))‖ ≤ q.divisors.card := by
  set f : ℕ → ℂ := fun k => (if IsUnit (k : ZMod q) then 1 else 0) - (q.totient : ℂ) / q with hf
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  rw [Ew_eq, sum_spl_mul A B ℓ r hℓ f, tup, Finset.sum_product_right]
  -- each `j` contributes the interval `(A + Σj, B + Σj]`
  have hj : ∀ j : Fin r → ℕ, ‖∑ i ∈ Ioc A B, f (tsum (i, j))‖ ≤ q.divisors.card := by
    intro j
    have e : ∑ i ∈ Ioc A B, f (tsum (i, j)) = ∑ k ∈ Ioc (A + ∑ m, j m) (B + ∑ m, j m), f k := by
      rw [← Finset.map_add_right_Ioc, Finset.sum_map]
      rfl
    rw [e]
    exact norm_sum_Ioc_unit_le _ _
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((ℓ : ℝ) ^ r)⁻¹ * ‖∑ j ∈ Fintype.piFinset (fun _ : Fin r => range ℓ), ∑ i ∈ Ioc A B, f (tsum (i, j))‖
      ≤ ((ℓ : ℝ) ^ r)⁻¹ * ∑ _j ∈ Fintype.piFinset (fun _ : Fin r => range ℓ), (q.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hj j)) (by positivity)
    _ = q.divisors.card := by
        rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-! ### The estimate with a spline weight -/

omit [NeZero q] in
/-- An interval's residue classes: `#{k′ ∈ (C, D] : k′ ≡ k (mod q)} ≤ ⌊(D − C)/q⌋ + 1`. -/
theorem card_Ioc_filter_cong_le (C D k : ℕ) :
    #((Ioc C D).filter (fun k' : ℕ => (k' : ZMod q) = (k : ZMod q))) ≤ (D - C) / q + 1 := by
  -- `k′ ↦ ⌊(k′ − C − 1)/q⌋` is injective on a residue class
  calc #((Ioc C D).filter (fun k' : ℕ => (k' : ZMod q) = (k : ZMod q)))
      ≤ #(range ((D - C) / q + 1)) := by
        refine Finset.card_le_card_of_injOn (fun k' => (k' - (C + 1)) / q) ?_ ?_
        · intro k' hk'
          simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hk'
          simp only [Finset.coe_range, Set.mem_Iio]
          have : (k' - (C + 1)) / q ≤ (D - C) / q := Nat.div_le_div_right (by omega)
          omega
        · intro x hx y hy hxy
          simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hx hy
          simp only at hxy
          have hxy' : (x : ZMod q) = (y : ZMod q) := hx.2.trans hy.2.symm
          rw [ZMod.natCast_eq_natCast_iff] at hxy'
          have hm : x - (C + 1) ≡ y - (C + 1) [MOD q] := by
            refine Nat.ModEq.add_right_cancel' (C + 1) ?_
            rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
          have e1 := Nat.div_add_mod (x - (C + 1)) q
          have e2 := Nat.div_add_mod (y - (C + 1)) q
          rw [hxy, show (x - (C + 1)) % q = (y - (C + 1)) % q from hm] at e1
          omega
    _ = (D - C) / q + 1 := Finset.card_range _

/-- The spline's support has `B + r(ℓ − 1) − A` elements, at most `⌊(B + r(ℓ − 1) − A)/q⌋ + 1` in a residue class,
and `Σ|w|² ≤ B + r(ℓ − 1) − A`; so `q⁻¹Σ_h|ŵ(h)|² ≤ (⌊n/q⌋ + 1)n`, `n = B + r(ℓ − 1) − A`. -/
theorem sum_norm_what_spl_le (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) :
    (q : ℝ)⁻¹ * ∑ h : ZMod q, ‖what (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ)) h‖ ^ 2 ≤
      (((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 := sum_norm_what_sq_le (q := q) (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ))
    (M := (B + r * (ℓ - 1) - A) / q + 1) (fun k _ => card_Ioc_filter_cong_le _ _ _)
  have h2 : ∑ k ∈ supp A B ℓ r, ‖((spl A B ℓ r k : ℝ) : ℂ)‖ ^ 2 ≤ (B + r * (ℓ - 1) - A : ℕ) := by
    calc ∑ k ∈ supp A B ℓ r, ‖((spl A B ℓ r k : ℝ) : ℂ)‖ ^ 2 ≤ ∑ _k ∈ supp A B ℓ r, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (spl_nonneg _ _ _ _ _)]
          have := spl_le_one A B ℓ r k hℓ
          have := spl_nonneg A B ℓ r k
          nlinarith
      _ = (B + r * (ℓ - 1) - A : ℕ) := by rw [Finset.sum_const, nsmul_one, supp, Nat.card_Ioc]
  calc (q : ℝ)⁻¹ * ∑ h : ZMod q, ‖what (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ)) h‖ ^ 2
      ≤ (q : ℝ)⁻¹ * (q * ((((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) *
          ∑ k ∈ supp A B ℓ r, ‖((spl A B ℓ r k : ℝ) : ℂ)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * ∑ k ∈ supp A B ℓ r, ‖((spl A B ℓ r k : ℝ) : ℂ)‖ ^ 2 := by
        field_simp
    _ ≤ (((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The bilinear Type I estimate with a spline weight.** In `SieveTypeIB.typeIB_bound` take `S = (A, B + r(ℓ − 1)]`
and `w` the spline (`ℓ ≥ 1`). Then `|Σ_{d₁,d₂} α(d₁)β(d₂)Σ_k w(k)dw(d₁d₂k)|` is at most
`(Σ|α|²)^{1/2}(mF(Σ|β|²)(⌊n/q⌋ + 1)n)^{1/2} + (B − A)(q/(2ℓ(H + 1)))^r(Σ|α|)(Σ|β|) + |Σα||Σβ|d(q)/φ(q)`, with
`n = B + r(ℓ − 1) − A`. -/
theorem typeIB_spline (a : ZMod q) (ha : IsUnit a) (D₁ D₂ : Finset ℕ) (α β : ℕ → ℂ)
    (hD₁ : ∀ d ∈ D₁, IsUnit (d : ZMod q)) (hD₂ : ∀ d ∈ D₂, IsUnit (d : ZMod q)) (hD₂0 : ∀ d ∈ D₂, 0 < d)
    (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {H Dm F m : ℕ}
    (hDm : ∀ d ∈ D₂, d ≤ Dm) (hDm1 : 1 ≤ Dm) (hq : 2 * H * Dm < q)
    (hm : ∀ r : ZMod q, #(D₁.filter (fun d : ℕ => ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F) :
    ‖∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ *
        ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (d₁ * d₂ * k)‖ ≤
      √(∑ d ∈ D₁, ‖α d‖ ^ 2) * √(m * F * (∑ d ∈ D₂, ‖β d‖ ^ 2) *
          ((((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ))) +
        ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r * ((∑ d ∈ D₁, ‖α d‖) * (∑ d ∈ D₂, ‖β d‖)) +
        ‖∑ d ∈ D₁, α d‖ * ‖∑ d ∈ D₂, β d‖ * (q.divisors.card / q.totient) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hb := typeIB_bound a ha D₁ D₂ α β hD₁ hD₂ hD₂0 (supp A B ℓ r) (fun k => ((spl A B ℓ r k : ℝ) : ℂ))
    (H := H) (Dm := Dm) (F := F) (m := m) (W := ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r)
    (by positivity) hDm hDm1 hq hm hF (fun h h0 hH => norm_what_spl_tail A B ℓ r H hℓ h h0 hH)
  refine hb.trans (add_le_add (add_le_add ?_ le_rfl) ?_)
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left (sum_norm_what_spl_le A B ℓ r hℓ) (by positivity)
  · rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (norm_Ew_spl_le A B ℓ r hℓ) hφ.le)
      (by positivity)

end SieveSpline
