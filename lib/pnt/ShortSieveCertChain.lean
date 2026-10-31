import ShortSieveCertDrop
import ShortSieveChain

/-!
# The chain bound of a dropped standard node

The primes of a standard node are ordered, `p₀ > p₁ > ⋯ > p_k`, and a dropped node's loss is `ω*` times the sum over
its box of `log x/(p₀ ⋯ p_k log p_k)` (`ShortSieveDrop.count_le_drop1`). The product of the primes' Mertens sums
bounds that sum, but wastes the order where the primes' ranges overlap. The chain bound cuts the range at breakpoints
`e₀ ≤ e₁ ≤ ⋯` (the ends of the ranges): the primes in one interval `[x^{e_t/DEN}, x^{e_{t+1}/DEN})` form a run, and a
run of `r` primes costs at most the least of the product of its members' sums and
`(DEN/e_t)^{n₂} trB(e_t, e_{t+1})^r/r!` (`n₂ = 1` if it holds the sifting prime). The sum over the box is then at most
the dynamic programme over the intervals and the runs.

* `dpStep`, `dpRun`: the programme in fixed point (units `1/SC`), and its soundness (`dpStep_sound`, `dpRun_sound`)
  from the exact split of a chain at a threshold (`ShortSieveChain.chainSum_split`), for any run bounds.
* `rbStd`: the run bounds of a standard node's primes, and their soundness (`evLe_rbStd`).
* `Sound.OK_of_dropC`: **a dropped standard node** has the loss `ω*` times any limit superior of its chain sum.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree ShortSieveChain SieveRough

/-! ### Fixed point -/

/-- The fixed-point unit of the losses, `2^{50}`. -/
def SC : ℕ := 2 ^ 50


/-- A product in units `1/SC`, each step rounded up. -/
def prodSC (fs : List ℕ) : ℕ := fs.foldl (fun acc f => SieveCert.cdiv (acc * f) SC) SC

/-- The factor `trB(lo, hi)` of a prime of a dropped node in units `1/SC`, rounded up. -/
def trF (lo hi : ℤ) : ℕ := SieveCert.cdiv (SC * (hi.toNat - lo.toNat) * (hi.toNat + lo.toNat)) (2 * lo.toNat * hi.toNat)

/-- The factor `DEN/lo − DEN/hi` of a sifting prime of a dropped node in units `1/SC`, rounded up. -/
def invF (lo hi : ℤ) : ℕ := SieveCert.cdiv (SC * DEN * (hi.toNat - lo.toNat)) (lo.toNat * hi.toNat)


theorem SC_pos : (0 : ℝ) < SC := by norm_num [SC]

theorem foldl_SC_ge : ∀ (fs : List ℕ) (acc : ℕ),
    (acc : ℝ) / SC * (fs.map fun f : ℕ => (f : ℝ) / SC).prod ≤
      ((fs.foldl (fun acc f => SieveCert.cdiv (acc * f) SC) acc : ℕ) : ℝ) / SC
  | [], acc => by simp
  | f :: fs, acc => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    refine le_trans ?_ (foldl_SC_ge fs _)
    have h := SieveOmegaB.div_le_cdiv (acc * f) SC (by norm_num [SC])
    push_cast at h
    have hp : 0 ≤ (fs.map fun f : ℕ => (f : ℝ) / SC).prod := List.prod_nonneg fun x hx => by
      obtain ⟨f', -, rfl⟩ := List.mem_map.1 hx
      positivity
    have hS := SC_pos
    calc (acc : ℝ) / SC * ((f : ℝ) / SC * (fs.map fun f : ℕ => (f : ℝ) / SC).prod)
        = ((acc : ℝ) * f / SC) / SC * (fs.map fun f : ℕ => (f : ℝ) / SC).prod := by ring
      _ ≤ (SieveCert.cdiv (acc * f) SC : ℝ) / SC * (fs.map fun f : ℕ => (f : ℝ) / SC).prod := by gcongr

/-- **The fixed-point product** bounds the product of the factors. -/
theorem prod_le_prodSC (fs : List ℕ) : (fs.map fun f : ℕ => (f : ℝ) / SC).prod ≤ (prodSC fs : ℝ) / SC := by
  have h := foldl_SC_ge fs SC
  rw [div_self SC_pos.ne', one_mul] at h
  exact h

theorem list_prod_map_range (g : ℕ → ℝ) : ∀ n : ℕ, ((List.range n).map g).prod = ∏ i ∈ range n, g i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, list_prod_map_range g n, prod_range_succ]; simp

theorem trB_le_trF {lo hi : ℤ} (hlo : 0 < lo) (hlh : lo ≤ hi) : trB lo hi ≤ (trF lo hi : ℝ) / SC := by
  have hl : ((lo.toNat : ℕ) : ℝ) = lo := by exact_mod_cast Int.toNat_of_nonneg hlo.le
  have hh : ((hi.toNat : ℕ) : ℝ) = hi := by exact_mod_cast Int.toNat_of_nonneg (hlo.le.trans hlh)
  have hlh' : lo.toNat ≤ hi.toNat := by omega
  have hl0 : 0 < lo.toNat := by omega
  have hh0 : 0 < hi.toNat := by omega
  have hpos : 0 < 2 * lo.toNat * hi.toNat := by positivity
  have h := SieveOmegaB.div_le_cdiv (SC * (hi.toNat - lo.toNat) * (hi.toNat + lo.toNat)) (2 * lo.toNat * hi.toNat)
    hpos
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hlh', Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hl, hh] at h
  unfold trF
  have hS := SC_pos
  rw [le_div_iff₀ hS]
  refine le_trans (le_of_eq ?_) h
  unfold trB
  push_cast
  field_simp

theorem inv_le_invF {lo hi : ℤ} (hlo : 0 < lo) (hlh : lo ≤ hi) :
    (DEN : ℝ) / lo - DEN / hi ≤ (invF lo hi : ℝ) / SC := by
  have hl : ((lo.toNat : ℕ) : ℝ) = lo := by exact_mod_cast Int.toNat_of_nonneg hlo.le
  have hh : ((hi.toNat : ℕ) : ℝ) = hi := by exact_mod_cast Int.toNat_of_nonneg (hlo.le.trans hlh)
  have hlh' : lo.toNat ≤ hi.toNat := by omega
  have hl0 : 0 < lo.toNat := by omega
  have hh0 : 0 < hi.toNat := by omega
  have hpos : 0 < lo.toNat * hi.toNat := by positivity
  have h := SieveOmegaB.div_le_cdiv (SC * DEN * (hi.toNat - lo.toNat)) (lo.toNat * hi.toNat) hpos
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hlh', Nat.cast_mul, hl, hh] at h
  unfold invF
  have hS := SC_pos
  have hlo' : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hhi' : (0 : ℝ) < hi := by exact_mod_cast hlo.trans_le hlh
  rw [le_div_iff₀ hS]
  refine le_trans (le_of_eq ?_) h
  field_simp

/-! ### The dynamic programme over the breakpoints -/

/-- The threshold `⌈x^{e/DEN}⌉` of the breakpoint `e`. -/
noncomputable def thr (x : ℝ) (e : ℤ) : ℕ := ⌈x ^ ((e : ℝ) / DEN)⌉₊

theorem thr_mono {x : ℝ} (hx : 1 ≤ x) {e f : ℤ} (h : e ≤ f) : thr x e ≤ thr x f :=
  Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hx
    (div_le_div_of_nonneg_right (by exact_mod_cast h) DEN_pos.le))

/-- One step of the programme, over an interval whose runs `j, …, j + r − 1` have the bounds `RB j r` (units
`1/SC`): `P'_j = P_j + Σ_{1 ≤ r ≤ m − j} ⌈RB_{j,r} P_{j+r}/SC⌉` for `j ≤ m`. -/
def dpStep (m : ℕ) (RB : ℕ → ℕ → ℕ) (P : List ℕ) : List ℕ :=
  (List.range (m + 1)).map fun j => P.getD j 0 +
    ((List.range (m - j)).map fun i => SieveCert.cdiv (RB j (i + 1) * P.getD (j + i + 1) 0) SC).sum

/-- **The chain bound's programme** over the intervals between consecutive breakpoints, the run bounds `RB e f j r`
on `[e, f)`. -/
def dpRun (m : ℕ) (RB : ℤ → ℤ → ℕ → ℕ → ℕ) : ℤ → List ℤ → List ℕ → List ℕ
  | _, [], P => P
  | e, f :: rest, P => dpRun m RB f rest (dpStep m (RB e f) P)

/-- The breakpoints increase. -/
def incr : ℤ → List ℤ → Bool
  | _, [] => true
  | e, f :: rest => decide (e ≤ f) && incr f rest

/-- The last breakpoint. -/
def lastD : ℤ → List ℤ → ℤ
  | e, [] => e
  | _, f :: rest => lastD f rest

theorem getD_dpStep (m : ℕ) (RB : ℕ → ℕ → ℕ) (P : List ℕ) {j : ℕ} (hj : j ≤ m) :
    (dpStep m RB P).getD j 0 = P.getD j 0 +
      ((List.range (m - j)).map fun i => SieveCert.cdiv (RB j (i + 1) * P.getD (j + i + 1) 0) SC).sum := by
  unfold dpStep
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- **A step of the programme is sound**: from the bounds of the chains' sums below `e` and the runs' bounds on
`[e, f)`, the bounds below `f`. -/
theorem dpStep_sound {m : ℕ} {Mx : ℝ → ℕ → Finset ℕ × (ℕ → ℝ)} (hw : ∀ᶠ x : ℝ in atTop, ∀ i p, 0 ≤ (Mx x i).2 p)
    {RB : ℕ → ℕ → ℕ} {e f : ℤ} (hef : e ≤ f) {P : List ℕ}
    (hRB : ∀ j < m, ∀ r, 1 ≤ r → r ≤ m - j →
      EvLe (fun x => runSum r (sfx (Mx x) m j) (thr x e) (thr x f)) (RB j r / SC))
    (hP : ∀ j ≤ m, EvLe (fun x => chainSum (sfx (Mx x) m j) (thr x e)) (P.getD j 0 / SC)) :
    ∀ j ≤ m, EvLe (fun x => chainSum (sfx (Mx x) m j) (thr x f)) ((dpStep m RB P).getD j 0 / SC) := by
  intro j hj
  rw [getD_dpStep m RB P hj]
  have hsplit : ∀ᶠ x : ℝ in atTop, chainSum (sfx (Mx x) m j) (thr x f) =
      chainSum (sfx (Mx x) m j) (thr x e) + ∑ i ∈ range (m - j),
        runSum (i + 1) (sfx (Mx x) m j) (thr x e) (thr x f) * chainSum (sfx (Mx x) m (j + i + 1)) (thr x e) := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [chainSum_split _ (thr_mono hx hef), length_sfx, sum_range_succ', add_comm]
    congr 1
    · simp [runSum]
    · refine sum_congr rfl fun i _ => ?_
      rw [drop_sfx]
      rfl
  have hS := SC_pos
  have hsum : EvLe (fun x => ∑ i ∈ range (m - j), runSum (i + 1) (sfx (Mx x) m j) (thr x e) (thr x f) *
      chainSum (sfx (Mx x) m (j + i + 1)) (thr x e))
      (∑ i ∈ range (m - j), (RB j (i + 1) : ℝ) / SC * ((P.getD (j + i + 1) 0 : ℝ) / SC)) := by
    refine evLe_sum _ _ _ fun i hi => ?_
    have hi' := mem_range.1 hi
    refine EvLe.mul (by positivity) (by positivity) ?_ ?_ (hRB j (by omega) (i + 1) (by omega) (by omega))
      (hP (j + i + 1) (by omega))
    · filter_upwards [hw] with x hx
      exact runSum_nonneg _ _ (fun M hM p => by obtain ⟨i', -, -, rfl⟩ := mem_sfx hM; exact hx i' p) _ _
    · filter_upwards [hw] with x hx
      exact chainSum_nonneg _ (fun M hM p => by obtain ⟨i', -, -, rfl⟩ := mem_sfx hM; exact hx i' p) _
  refine evLe_mono (evLe_of_le (evLe_add (hP j hj) hsum) (hsplit.mono fun x hx => le_of_eq hx)) ?_
  rw [Nat.cast_add, add_div, Nat.cast_list_sum, List.map_map, list_sum_map_range, sum_div]
  refine add_le_add le_rfl (sum_le_sum fun i _ => ?_)
  have h := SieveOmegaB.div_le_cdiv (RB j (i + 1) * P.getD (j + i + 1) 0) SC (by norm_num [SC])
  push_cast at h
  calc (RB j (i + 1) : ℝ) / SC * ((P.getD (j + i + 1) 0 : ℝ) / SC)
      = ((RB j (i + 1) : ℝ) * P.getD (j + i + 1) 0 / SC) / SC := by ring
    _ ≤ _ := div_le_div_of_nonneg_right h hS.le

/-- **The programme is sound**: from the bounds below the first breakpoint, the bounds below the last, for run bounds
that hold on every interval `[e, f)`, `0 < e ≤ f`, and increasing positive breakpoints. -/
theorem dpRun_sound {m : ℕ} {Mx : ℝ → ℕ → Finset ℕ × (ℕ → ℝ)} (hw : ∀ᶠ x : ℝ in atTop, ∀ i p, 0 ≤ (Mx x i).2 p)
    {RB : ℤ → ℤ → ℕ → ℕ → ℕ}
    (hRB : ∀ e f : ℤ, 0 < e → e ≤ f → ∀ j < m, ∀ r, 1 ≤ r → r ≤ m - j →
      EvLe (fun x => runSum r (sfx (Mx x) m j) (thr x e) (thr x f)) (RB e f j r / SC)) :
    ∀ (e : ℤ) (rest : List ℤ) (P : List ℕ), 0 < e → (∀ f ∈ rest, 0 < f) → incr e rest = true →
    (∀ j ≤ m, EvLe (fun x => chainSum (sfx (Mx x) m j) (thr x e)) (P.getD j 0 / SC)) →
    ∀ j ≤ m, EvLe (fun x => chainSum (sfx (Mx x) m j) (thr x (lastD e rest))) ((dpRun m RB e rest P).getD j 0 / SC)
  | e, [], P, _, _, _, hP => by simpa [dpRun, lastD] using hP
  | e, f :: rest, P, he, hpos, hch, hP => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at hch
    obtain ⟨hef, hch'⟩ := hch
    have := dpRun_sound hw hRB f rest (dpStep m (RB e f) P) (hpos f (by simp))
      (fun g hg => hpos g (by simp [hg])) hch' (dpStep_sound hw hef (hRB e f he hef) hP)
    simpa [dpRun, lastD] using this

/-! ### The run bounds of a standard node -/

/-- The members of a dropped standard node's chain: the primes of the box's ranges, with the weights `1/p` and, for
the sifting prime `k`, `log x/(p log p)`. -/
noncomputable def stdMem (B : Box) (k : ℕ) (x : ℝ) (i : ℕ) : Finset ℕ × (ℕ → ℝ) :=
  (primesIn (x ^ (((B.getD i (0, 0)).1 : ℝ) / DEN)) (x ^ (((B.getD i (0, 0)).2 : ℝ) / DEN)),
    if i = k then fun p => Real.log x / (p * Real.log p) else fun p => 1 / p)

/-- The factor of the member `i` on `[e, f)`: its range clipped to the interval, units `1/SC`. -/
def clipF (B : Box) (k : ℕ) (e f : ℤ) (i : ℕ) : ℕ :=
  if i = k then invF (max (B.getD i (0, 0)).1 e) (min (B.getD i (0, 0)).2 f)
  else trF (max (B.getD i (0, 0)).1 e) (min (B.getD i (0, 0)).2 f)

/-- The ordered bound of the run of the members `j, …, j + r − 1` on `[e, f)`, units `1/SC`:
`(DEN/e)^{n₂} trB(e, f)^r/r!`, with `n₂ = 1` if the run holds the sifting prime `k`. -/
def ordF (k : ℕ) (e f : ℤ) (j r : ℕ) : ℕ :=
  SieveCert.cdiv (if j ≤ k ∧ k < j + r then SieveCert.cdiv (prodSC (List.replicate r (trF e f)) * DEN) e.toNat
    else prodSC (List.replicate r (trF e f))) r.factorial

/-- **The run bounds of a standard node**: the least of the product of the clipped factors and the ordered bound. -/
def rbStd (B : Box) (k : ℕ) (e f : ℤ) (j r : ℕ) : ℕ :=
  min (prodSC ((List.range r).map fun i => clipF B k e f (j + i))) (ordF k e f j r)

theorem rpow_div_max {x : ℝ} (hx : 1 ≤ x) (a b : ℤ) :
    x ^ (((max a b : ℤ) : ℝ) / DEN) = max (x ^ ((a : ℝ) / DEN)) (x ^ ((b : ℝ) / DEN)) := by
  rw [Int.cast_max, ← max_div_div_right DEN_pos.le]
  exact Monotone.map_max fun s t h => Real.rpow_le_rpow_of_exponent_le hx h

theorem rpow_div_min {x : ℝ} (hx : 1 ≤ x) (a b : ℤ) :
    x ^ (((min a b : ℤ) : ℝ) / DEN) = min (x ^ ((a : ℝ) / DEN)) (x ^ ((b : ℝ) / DEN)) := by
  rw [Int.cast_min, ← min_div_div_right DEN_pos.le]
  exact Monotone.map_min fun s t h => Real.rpow_le_rpow_of_exponent_le hx h

/-- The primes of a range between two thresholds are the primes of the clipped range. -/
theorem filter_primesIn_thr {x : ℝ} (hx : 1 ≤ x) (lo hi e f : ℤ) :
    (primesIn (x ^ ((lo : ℝ) / DEN)) (x ^ ((hi : ℝ) / DEN))).filter (fun p => thr x e ≤ p ∧ p < thr x f) =
      primesIn (x ^ (((max lo e : ℤ) : ℝ) / DEN)) (x ^ (((min hi f : ℤ) : ℝ) / DEN)) := by
  ext p
  simp only [mem_filter, mem_primesIn, thr, Nat.ceil_le, Nat.lt_ceil, rpow_div_max hx, rpow_div_min hx, max_le_iff,
    lt_min_iff]
  tauto

/-- **A member's sum on an interval** is at most its clipped factor. -/
theorem evLe_clip (B : Box) (k : ℕ) {e f : ℤ} (he : 0 < e) (i : ℕ) :
    EvLe (fun x => ∑ p ∈ (stdMem B k x i).1.filter (fun p => thr x e ≤ p ∧ p < thr x f), (stdMem B k x i).2 p)
      (clipF B k e f i / SC) := by
  have hset : ∀ᶠ x : ℝ in atTop, (stdMem B k x i).1.filter (fun p => thr x e ≤ p ∧ p < thr x f) =
      primesIn (x ^ (((max (B.getD i (0, 0)).1 e : ℤ) : ℝ) / DEN))
        (x ^ (((min (B.getD i (0, 0)).2 f : ℤ) : ℝ) / DEN)) := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact filter_primesIn_thr hx _ _ e f
  unfold clipF
  set a := max (B.getD i (0, 0)).1 e with ha
  set b := min (B.getD i (0, 0)).2 f with hb
  have ha0 : 0 < a := lt_of_lt_of_le he (le_max_right _ _)
  have hD := DEN_pos
  have ha0r : (0 : ℝ) < a := by exact_mod_cast ha0
  have ha0' : (0 : ℝ) < (a : ℝ) / DEN := div_pos ha0r hD
  by_cases hab : a ≤ b
  · have hb0r : (0 : ℝ) < b := by exact_mod_cast ha0.trans_le hab
    have hab' : (a : ℝ) / DEN ≤ (b : ℝ) / DEN := div_le_div_of_nonneg_right (by exact_mod_cast hab) hD.le
    by_cases hik : i = k
    · have h := evLe_sum_inv_log ha0' hab'
      refine evLe_of_le (evLe_mono h ?_) ?_
      · have e1 : 1 / ((a : ℝ) / DEN) - 1 / ((b : ℝ) / DEN) = (DEN : ℝ) / a - DEN / b := by
          rw [one_div_div, one_div_div]
        rw [e1, ite_eq_left hik]
        exact inv_le_invF ha0 hab
      · filter_upwards [hset] with x hx
        rw [hx, mul_sum]
        refine le_of_eq (sum_congr rfl fun p _ => ?_)
        simp only [stdMem, ite_eq_left hik]
        rw [mul_one_div]
    · have h := evLe_sum_inv ha0' hab'
      refine evLe_of_le (evLe_mono h ?_) ?_
      · rw [ite_eq_right hik]
        have h1 := log_le_trB ha0r (by exact_mod_cast hab : (a : ℝ) ≤ b)
        have h2 := trB_le_trF ha0 hab
        have e1 : Real.log ((b : ℝ) / DEN) - Real.log ((a : ℝ) / DEN) = Real.log b - Real.log a := by
          rw [Real.log_div hb0r.ne' hD.ne', Real.log_div ha0r.ne' hD.ne']
          ring
        rw [e1]
        exact h1.trans h2
      · filter_upwards [hset] with x hx
        rw [hx]
        refine le_of_eq (sum_congr rfl fun p _ => ?_)
        simp only [stdMem, ite_eq_right hik]
  · -- the clipped range is empty
    refine fun δ hδ => ?_
    filter_upwards [hset, eventually_ge_atTop 1] with x hx hx1
    rw [hx]
    have hemp : primesIn (x ^ ((a : ℝ) / DEN)) (x ^ ((b : ℝ) / DEN)) = ∅ := by
      ext p
      simp only [mem_primesIn, Finset.notMem_empty, iff_false, not_and, not_lt]
      intro _ hp
      refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1 ?_) hp
      exact div_le_div_of_nonneg_right (by exact_mod_cast (not_le.1 hab).le) hD.le
    rw [hemp, sum_empty]
    have : (0 : ℝ) ≤ (if i = k then invF a b else trF a b : ℕ) / SC := by positivity
    linarith

theorem stdMem_nonneg (B : Box) (k : ℕ) : ∀ᶠ x : ℝ in atTop, ∀ i p, 0 ≤ (stdMem B k x i).2 p := by
  filter_upwards [eventually_ge_atTop 1] with x hx i p
  unfold stdMem
  split_ifs
  · exact div_nonneg (Real.log_nonneg hx) (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  · positivity

/-- **A run's product bound**: the product of its members' clipped factors. -/
theorem evLe_run_prod (B : Box) (k : ℕ) {e f : ℤ} (he : 0 < e) {j r : ℕ} (hr : r ≤ k + 1 - j) :
    EvLe (fun x => runSum r (sfx (stdMem B k x) (k + 1) j) (thr x e) (thr x f))
      (prodSC ((List.range r).map fun i => clipF B k e f (j + i)) / SC) := by
  have hle : ∀ᶠ x : ℝ in atTop, runSum r (sfx (stdMem B k x) (k + 1) j) (thr x e) (thr x f) ≤
      ∏ i ∈ range r, ∑ p ∈ (stdMem B k x (j + i)).1.filter (fun p => thr x e ≤ p ∧ p < thr x f),
        (stdMem B k x (j + i)).2 p := by
    filter_upwards [stdMem_nonneg B k] with x hx
    have h := runSum_le_prod r (sfx (stdMem B k x) (k + 1) j) (thr x e) (thr x f) (thr x f) le_rfl
      (fun M hM p => by obtain ⟨i, -, -, rfl⟩ := mem_sfx hM; exact hx i p)
    rwa [prod_take_sfx, min_eq_left hr] at h
  have hprod : EvLe (fun x => ∏ i ∈ range r, ∑ p ∈ (stdMem B k x (j + i)).1.filter
      (fun p => thr x e ≤ p ∧ p < thr x f), (stdMem B k x (j + i)).2 p)
      (∏ i ∈ range r, (clipF B k e f (j + i) : ℝ) / SC) := by
    have h := EvLe.prod (fun (t : Fin r) x => ∑ p ∈ (stdMem B k x (j + t)).1.filter
      (fun p => thr x e ≤ p ∧ p < thr x f), (stdMem B k x (j + t)).2 p)
      (fun t => (clipF B k e f (j + t) : ℝ) / SC) (fun t => by positivity)
      (fun t => by
        filter_upwards [stdMem_nonneg B k] with x hx
        exact sum_nonneg fun p _ => hx _ p)
      (fun t => evLe_clip B k he (j + t))
    simpa only [Finset.prod_range] using h
  refine evLe_mono (evLe_of_le hprod hle) ?_
  have h := prod_le_prodSC ((List.range r).map fun i => clipF B k e f (j + i))
  rwa [List.map_map, Function.comp_def, list_prod_map_range] at h

theorem prod_range_window (j k : ℕ) (a : ℝ) : ∀ r : ℕ,
    ∏ i ∈ range r, (if j + i = k then a else 1) = if j ≤ k ∧ k < j + r then a else 1
  | 0 => by
    rw [prod_range_zero, ite_eq_right (by omega)]
  | r + 1 => by
    rw [prod_range_succ, prod_range_window j k a r]
    by_cases h1 : j + r = k
    · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left (by omega), one_mul]
    · rw [ite_eq_right h1, mul_one]
      by_cases h2 : j ≤ k ∧ k < j + r
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- **A run's ordered bound**: its primes are strictly decreasing in `[x^{e/DEN}, x^{f/DEN})`, so the run is at most
`(DEN/e)^{n₂} (Σ 1/p)^r/r!`. -/
theorem evLe_run_ord (B : Box) (k : ℕ) {e f : ℤ} (he : 0 < e) (hef : e ≤ f) {j r : ℕ} (hr : r ≤ k + 1 - j) :
    EvLe (fun x => runSum r (sfx (stdMem B k x) (k + 1) j) (thr x e) (thr x f)) (ordF k e f j r / SC) := by
  have hD := DEN_pos
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have he' : (0 : ℝ) < (e : ℝ) / DEN := div_pos heR hD
  have hef' : (e : ℝ) / DEN ≤ (f : ℝ) / DEN := div_le_div_of_nonneg_right (by exact_mod_cast hef) hD.le
  set C : ℝ := if j ≤ k ∧ k < j + r then (DEN : ℝ) / e else 1 with hC
  have hC0 : 0 ≤ C := by rw [hC]; split_ifs <;> positivity
  set c : ℕ → ℝ := fun i => if i = k then (DEN : ℝ) / e else 1 with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by rw [hc]; dsimp only; split_ifs <;> positivity
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  -- pointwise: the run is at most `C (Σ_{x^{e/DEN} ≤ p < x^{f/DEN}} 1/p)^r/r!`
  have hle : ∀ᶠ x : ℝ in atTop, runSum r (sfx (stdMem B k x) (k + 1) j) (thr x e) (thr x f) ≤
      C * ((∑ p ∈ primesIn (x ^ ((e : ℝ) / DEN)) (x ^ ((f : ℝ) / DEN)), 1 / (p : ℝ)) ^ r / r.factorial) := by
    filter_upwards [eventually_gt_atTop 1, stdMem_nonneg B k] with x hx hw
    have hlx : 0 < Real.log x := Real.log_pos hx
    have h := runSum_sfx_le_dec (stdMem B k x) (k + 1) (primesIn (x ^ ((e : ℝ) / DEN)) (x ^ ((f : ℝ) / DEN)))
      (f := fun p => 1 / (p : ℝ)) (fun p => by positivity) c hc0 hw r j (thr x e) (thr x f)
      (fun i _ _ p hp hp1 hp2 => by
        have hp' := (mem_primesIn.1 hp).1
        have hxe : x ^ ((e : ℝ) / DEN) ≤ p := Nat.ceil_le.1 hp1
        refine ⟨mem_primesIn.2 ⟨hp', hxe, Nat.lt_ceil.1 hp2⟩, ?_⟩
        simp only [stdMem, hc]
        by_cases hik : i = k
        · rw [ite_eq_left hik, ite_eq_left hik]
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
          have hlp : (e : ℝ) / DEN * Real.log x ≤ Real.log p := by
            rw [← Real.log_rpow (by linarith)]
            exact Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hxe
          have hlp0 : 0 < Real.log p := lt_of_lt_of_le (mul_pos he' hlx) hlp
          have key : (e : ℝ) * Real.log x ≤ DEN * Real.log p := by
            have := mul_le_mul_of_nonneg_left hlp hD.le
            rw [← mul_assoc, mul_div_cancel₀ _ hD.ne'] at this
            exact this
          show Real.log x / (p * Real.log p) ≤ (DEN : ℝ) / e * (1 / p)
          rw [div_le_iff₀ (mul_pos hp0 hlp0)]
          calc Real.log x = (e * Real.log x) / e := by field_simp
            _ ≤ (DEN * Real.log p) / e := div_le_div_of_nonneg_right key heR.le
            _ = (DEN : ℝ) / e * (1 / p) * (p * Real.log p) := by field_simp
        · rw [ite_eq_right hik, ite_eq_right hik, one_mul])
    rw [min_eq_left hr, show (∏ i ∈ range r, c (j + i)) = C by
      rw [hC, ← prod_range_window j k ((DEN : ℝ) / e) r]] at h
    refine h.trans (mul_le_mul_of_nonneg_left ((decSum_le _ (fun p => by positivity) _ r _).trans
      (le_of_eq ?_)) hC0)
    rw [filter_true_of_mem fun p hp => by
      obtain ⟨-, h1, h2⟩ := mem_primesIn.1 hp
      exact ⟨Nat.ceil_le.2 h1, Nat.lt_ceil.2 h2⟩]
  -- the limit superior
  have hT : EvLe (fun x => ∑ p ∈ primesIn (x ^ ((e : ℝ) / DEN)) (x ^ ((f : ℝ) / DEN)), 1 / (p : ℝ))
      ((trF e f : ℝ) / SC) := by
    refine evLe_mono (evLe_sum_inv he' hef') ?_
    have hf0 : (0 : ℝ) < f := by exact_mod_cast he.trans_le hef
    have e1 : Real.log ((f : ℝ) / DEN) - Real.log ((e : ℝ) / DEN) = Real.log f - Real.log e := by
      rw [Real.log_div hf0.ne' hD.ne', Real.log_div heR.ne' hD.ne']
      ring
    rw [e1]
    exact (log_le_trB heR (by exact_mod_cast hef)).trans (trB_le_trF he hef)
  have hpow := evLe_pow (by positivity) (Eventually.of_forall fun x => sum_nonneg fun p _ => by positivity) hT r
  have h := evLe_const_mul (c := C / r.factorial) (by positivity) hpow
  refine evLe_mono (evLe_of_le h (hle.mono fun x hx => hx.trans (le_of_eq (by ring)))) ?_
  -- the fixed point
  set t := prodSC (List.replicate r (trF e f)) with ht
  have htr : ((trF e f : ℝ) / SC) ^ r ≤ (t : ℝ) / SC := by
    have := prod_le_prodSC (List.replicate r (trF e f))
    rwa [List.map_replicate, List.prod_replicate] at this
  have hS := SC_pos
  unfold ordF
  rw [← ht]
  have hcd := SieveOmegaB.div_le_cdiv (if j ≤ k ∧ k < j + r then SieveCert.cdiv (t * DEN) e.toNat else t)
    r.factorial (Nat.factorial_pos r)
  -- `C t/SC ≤ (the inner value)/SC`
  have hin : C * ((t : ℝ) / SC) ≤
      ((if j ≤ k ∧ k < j + r then SieveCert.cdiv (t * DEN) e.toNat else t : ℕ) : ℝ) / SC := by
    rw [hC]
    split_ifs with hn
    · have he0 : 0 < e.toNat := by omega
      have h2 := SieveOmegaB.div_le_cdiv (t * DEN) e.toNat he0
      have e2 : ((e.toNat : ℕ) : ℝ) = e := by exact_mod_cast Int.toNat_of_nonneg he.le
      push_cast at h2
      rw [e2] at h2
      calc (DEN : ℝ) / e * ((t : ℝ) / SC) = ((t : ℝ) * DEN / e) / SC := by ring
        _ ≤ _ := div_le_div_of_nonneg_right h2 hS.le
    · rw [one_mul]
  calc C / r.factorial * ((trF e f : ℝ) / SC) ^ r ≤ C / r.factorial * ((t : ℝ) / SC) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
    _ = (C * ((t : ℝ) / SC)) / r.factorial := by ring
    _ ≤ (((if j ≤ k ∧ k < j + r then SieveCert.cdiv (t * DEN) e.toNat else t : ℕ) : ℝ) / SC) / r.factorial :=
        div_le_div_of_nonneg_right hin hfac.le
    _ = (((if j ≤ k ∧ k < j + r then SieveCert.cdiv (t * DEN) e.toNat else t : ℕ) : ℝ) / r.factorial) / SC := by
        ring
    _ ≤ _ := div_le_div_of_nonneg_right hcd hS.le

/-- **The run bounds of a standard node are sound.** -/
theorem evLe_rbStd (B : Box) (k : ℕ) {e f : ℤ} (he : 0 < e) (hef : e ≤ f) {j r : ℕ} (hr : r ≤ k + 1 - j) :
    EvLe (fun x => runSum r (sfx (stdMem B k x) (k + 1) j) (thr x e) (thr x f)) (rbStd B k e f j r / SC) := by
  unfold rbStd
  rw [Nat.cast_min, ← min_div_div_right SC_pos.le]
  exact evLe_min (evLe_run_prod B k he hr) (evLe_run_ord B k he hef hr)

/-! ### The dropped standard node -/

open Classical in
/-- **A dropped standard node with the chain bound.** As `Sound.OK_of_drop`, with the primes ordered by the
constraints `ordCon j`: the loss is `Ω` times any limit superior `P` of the chain sum of the box's primes below
`x^{e/DEN}`, `e` at least the box's upper ends. -/
theorem Sound.OK_of_dropC {k : ℕ} {conds : List (Cond (k + 1) 1)} {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound (std k conds) (stdRows (k + 1)) E Γ B) (hE : 0 < E) (hinv : StdInv k conds)
    (hlen : k + 1 ≤ B.length) (hlo : ∀ j < k + 1, 0 < (B.getD j (0, 0)).1) (hord : ∀ j < k, ordCon j ∈ Γ)
    {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    (hn0 : 0 ≤ (numF k).minD B E acts) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hω : ∀ u : ℝ, ((numF k).minD B E acts : ℝ) / (B.getD k (0, 0)).2 ≤ u →
      u ≤ ((numF k).maxD B E acts : ℝ) / (B.getD k (0, 0)).1 → SieveCert.omegaC u ≤ Ω)
    {eK : ℤ} (heK : ∀ j < k + 1, (B.getD j (0, 0)).2 ≤ eK) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : EvLe (fun x => chainSum (sfx (stdMem B k x) (k + 1) 0) (thr x eK)) P)
    {θ ρ : ℝ} (hρ : 0 < ρ) (hρ25 : 12 * ρ < 1 / 25) :
    OK θ ρ 1 (fun x y => ((std k conds).count x y : ℝ)) (Ω * P) := by
  have hD := DEN_pos
  have hloR : ∀ j : Fin (k + 1), (0 : ℝ) < (B.getD j (0, 0)).1 := fun j => by exact_mod_cast hlo j j.isLt
  set PB : ℝ → Finset (Fin (k + 1) → ℕ) := fun x => (Fintype.piFinset fun j : Fin (k + 1) =>
    (stdMem B k x j).1).filter (fun p => StrictAnti p ∧ ∀ i, p i < thr x eK) with hPB
  -- the node's terms in the comparison interval
  have hterm : ∀ᶠ x : ℝ in atTop, ∀ v ∈ pairs (k + 1) 1 ⌊x⌋₊, SieveTree.rough (v.1 (Fin.last k)) (v.2 0) →
      (std k conds).InI x (x ^ (1 - ρ)) v.1 v.2 →
        v.1 ∈ PB x ∧ x ^ (1 / 25 : ℝ) ≤ v.1 (Fin.last k) ∧ (v.1 (Fin.last k) : ℝ) ≤ v.2 0 ∧
          SieveCert.omegaC (Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log (v.1 (Fin.last k))) ≤ Ω := by
    filter_upwards [abs_slack_le hE (k + 1) 1, eventually_gt_atTop 1,
      (tendsto_rpow_atTop hρ).eventually_ge_atTop 2] with x hsl hx1 hxr v hv _ hI
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx1
    obtain ⟨hp, hρ'⟩ := mem_pairs.1 hv
    have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
    have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ' i).1
    have hyx : x ^ (1 - ρ) ≤ x / 2 := by
      have e : x ^ (1 - ρ) * x ^ ρ = x := by rw [← Real.rpow_add hx0]; simp
      have : x ^ (1 - ρ) * 2 ≤ x := by
        calc x ^ (1 - ρ) * 2 ≤ x ^ (1 - ρ) * x ^ ρ := mul_le_mul_of_nonneg_left hxr (Real.rpow_nonneg hx0.le _)
          _ = x := e
      linarith
    obtain ⟨hcI, h1, h2⟩ := hI
    have hH := hsl v hv1 hv2 (by linarith) (by linarith)
    obtain ⟨hB, hΓ⟩ := h x hx1 v hv1 hv2 hcI hH
    obtain ⟨hall, hge⟩ := hinv x hx1 v hv1 hv2 hcI
    have hbox : ∀ j : Fin (k + 1), ((B.getD j (0, 0)).1 : ℝ) ≤ DEN * (Real.log (v.1 j) / Real.log x) ∧
        DEN * (Real.log (v.1 j) / Real.log x) < (B.getD j (0, 0)).2 := fun j => by
      rw [← coords_std x v j]
      exact inBox_getD B _ j hB (by have := j.isLt; omega)
    have hpj : ∀ j, (0 : ℝ) < v.1 j := fun j => by exact_mod_cast hv1 j
    have hlt : ∀ j : Fin (k + 1), (v.1 j : ℝ) < x ^ (((B.getD j (0, 0)).2 : ℝ) / DEN) := fun j =>
      lt_rpow_of_div_lt hx1 (hpj j) (by rw [lt_div_iff₀ hD]; linarith [(hbox j).2])
    refine ⟨mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => mem_primesIn.2 ⟨(hp j).2,
      rpow_le_of_le_div hx1 (hpj j) (by rw [div_le_iff₀ hD]; linarith [(hbox j).1]), hlt j⟩, ?_, fun i => ?_⟩,
      hall (Fin.last k), by exact_mod_cast hge, ?_⟩
    · -- the order of the primes
      refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
      have ho := (holds_ordCon i (coords (stdRows (k + 1)) x v) (slack x v)).1 (hΓ _ (hord i i.isLt))
      have e1 := coords_std x v i.succ
      have e2 := coords_std x v (Fin.castSucc i)
      simp only [Fin.val_succ, Fin.val_castSucc] at e1 e2
      rw [e1, e2] at ho
      have hl : Real.log (v.1 i.succ) < Real.log (v.1 (Fin.castSucc i)) := by
        have := lt_of_mul_lt_mul_left ho hD.le
        exact (div_lt_div_iff_of_pos_right hlx).1 this
      exact_mod_cast (Real.log_lt_log_iff (hpj _) (hpj _)).1 hl
    · -- below the last breakpoint
      refine Nat.lt_ceil.2 ((hlt i).trans_le (Real.rpow_le_rpow_of_exponent_le hx1.le ?_))
      exact div_le_div_of_nonneg_right (by exact_mod_cast heK i i.isLt) hD.le
    -- `u = (DEN − Σ_j X_j)/X_k`
    have hacts' : ∀ g ∈ acts, g.val (coords (stdRows (k + 1)) x v) (slack x v) ≤ 0 := fun g hg => by
      obtain ⟨c, hc', rfl⟩ := hacts g hg
      exact Con.val_le (hΓ c hc')
    have hfit : (numF k).c.length ≤ B.length := by simpa [numF] using hlen
    have hmin := (numF k).minD_le acts (inBoxC_of_inBox hB) hH hacts' hfit hfa
    have hmax := (numF k).le_maxD acts (inBoxC_of_inBox hB) hH hacts' hfit hfa
    set Nv := (numF k).val (coords (stdRows (k + 1)) x v) (slack x v) with hNv
    set D := DEN * (Real.log (v.1 (Fin.last k)) / Real.log x) with hD_def
    have hlogP : Real.log (∏ j, (v.1 j : ℝ)) = ∑ j, Real.log (v.1 j) :=
      Real.log_prod fun j _ => (hpj j).ne'
    have eN : Nv = DEN * (Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log x) := by
      rw [hNv, val_numF, Real.log_div hx0.ne' (prod_pos fun j _ => hpj j).ne', hlogP,
        ← Fin.sum_univ_eq_sum_range (fun j => coords (stdRows (k + 1)) x v j)]
      simp only [coords_std]
      rw [← mul_sum, ← sum_div]
      field_simp
    have hDpos : 0 < D := lt_of_lt_of_le (hloR (Fin.last k)) (by simpa using (hbox (Fin.last k)).1)
    have hu : Real.log (x / ∏ j, (v.1 j : ℝ)) / Real.log (v.1 (Fin.last k)) = Nv / D := by
      rw [eN, hD_def]
      have hlp : 0 < Real.log (v.1 (Fin.last k)) := by
        have := hDpos
        rw [hD_def] at this
        have h3 := pos_of_mul_pos_right this hD.le
        exact (div_pos_iff_of_pos_right hlx).1 h3
      field_simp
    rw [hu]
    have hDhi : D < (B.getD k (0, 0)).2 := by simpa using (hbox (Fin.last k)).2
    have hDlo : ((B.getD k (0, 0)).1 : ℝ) ≤ D := by simpa using (hbox (Fin.last k)).1
    have hn0' : (0 : ℝ) ≤ (numF k).minD B E acts := by exact_mod_cast hn0
    refine hω _ ?_ ?_
    · exact div_le_div₀ (hn0'.trans hmin) hmin hDpos hDhi.le
    · exact div_le_div₀ ((hn0'.trans hmin).trans hmax) hmax (hloR (Fin.last k)) (by simpa using hDlo)
  -- the sum over the ordered box is the chain sum
  have hsum : EvLe (fun x => ∑ p ∈ PB x, Real.log x / ((∏ j, (p j : ℝ)) * Real.log (p (Fin.last k)))) P := by
    refine evLe_of_le hP (Eventually.of_forall fun x => le_of_eq ?_)
    rw [← sum_filter_strictAnti (k + 1) (stdMem B k x) (thr x eK)]
    refine sum_congr rfl fun p _ => ?_
    have e1 : ∀ i : Fin k, (stdMem B k x (Fin.castSucc i : ℕ)).2 (p (Fin.castSucc i)) =
        1 / (p (Fin.castSucc i) : ℝ) := fun i => by
      simp only [stdMem, Fin.val_castSucc, ite_eq_right (ne_of_lt i.isLt)]
    have e2 : (stdMem B k x (Fin.last k : ℕ)).2 (p (Fin.last k)) =
        Real.log x / (p (Fin.last k) * Real.log (p (Fin.last k))) := by
      simp only [stdMem, Fin.val_last, ite_true]
    rw [Fin.prod_univ_castSucc (fun i : Fin (k + 1) => (stdMem B k x i).2 (p i)), e2,
      prod_congr rfl fun i _ => e1 i, Fin.prod_univ_castSucc (fun i : Fin (k + 1) => (p i : ℝ)), prod_div_distrib,
      prod_const_one]
    ring
  exact ShortSieveTree.OK_of_drop (fun x y => Nat.cast_nonneg _) fun δ hδ =>
    ShortSieveDrop.count_le_drop1 (fun _ => Fin.last k) conds (lo := 1 / 25) (by norm_num) hρ hρ25 hΩ hP0 _
      hterm hsum hδ

end ShortSieveCert
