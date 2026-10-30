/-
# The certificate to depth 8: its rule and its decisions

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The definitions are `SieveDeepDefs.lean`'s, on a grid of the certificate (`SieveCert.Grid`) with the
bilinear rule's exponent (`SieveCert.IBPar`).

* `lit_eq`, `nmin_eq`, `nmax_eq`, `bit_eq`, `testBit_bits`: `lit n f = f n`, `nmin` and `nmax` are `min` and `max`,
  `bit` is `Nat.testBit`, and `bits a b` has the bits `a, …, b`.
* `ibOK_append`: for boxes `ys` and `zs` with `tstar ys = some T`, a subset sum `s` of `ys`, and the estimate
  `condIB` at the split of `ys ++ zs` into `s` and the rest, with `e` (exponent `T`) on either side and `zs` on either
  side, `ibOK` passes `ys ++ zs`: `tstar (ys ++ zs) ≤ T`, and `condIB` is monotone.
* `dcp_sound`, `dmax3_sound`: `D < dcp a₁ a₂` gives the estimate at `(a₁ + D, a₂)` or `(a₁, a₂ + D)`, and
  `D < dmax3 i j k` gives the hypothesis of `ibOK_append` for `ys = (i, j, k)` and any `zs` with upper sum `D`.
* `okIB_of_okD`: **the block test is sound**: a box `(i, j, k) ++ zs` that passes `okD` (with `D` the upper sum of
  `zs` and `h` the box's last upper end) passes the bilinear rule `okIB`.
* `okD_mono`, `cstar_sound`: `okD` passes smaller deeper sums and last ends, and `c < cstar` gives `okD` on the worst
  box of depth 7 below `(…, b)`.
* `surelyEval4_of_lmask`, `surelyEval5_of_emask`, `surelyEval6_of_emask`: **the masks are sound**, for `HC = 4H`: a bit
  of `lmask`, `emask 1` or `emask 2` makes the box of depth 4, 5 or 6 surely evaluable. The bit comes from a global
  mask (`lbase`, `sbase`) shifted by the index sum of a set of the box's cells (`lbase_bit`, `smask_bit`), and the set
  with the deeper cells is a subset sum of the box (`mem_subsetSums_sel`).
* `lt_creg_iff`, `lt_lreg_iff`, `lt_bcnt_iff`, `inKK5_iff`: the regions in closed form, for `HC = 4H`.
* `dec4D`, `dec6D`, `scheme`: **the certificate's decisions** at depths 4 and 6 (those of `cost4` and `vR`), with
  `decD` at depth 2, as a scheme of `SieveBuch8.lean` under the bilinear rule: each passes the rule on the boxes it
  decomposes (`allowedR_of_decD`, `allowed4R_of_dec4D`, `allowed6R_of_dec6D`), by the block test and the masks.

The file imports `SieveDeepDefs.lean` and `SieveBuch8.lean`.
-/
import SieveDeepDefs
import SieveBuch8

namespace SieveDeep

open SieveCert

/-! ### Evaluation helpers -/

theorem lit_eq (n : ℕ) (f : ℕ → ℕ) : lit n f = f n := by cases n <;> rfl

theorem ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h

theorem ble_false {a b : ℕ} (h : b < a) : Nat.ble a b = false := by
  cases hc : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hc) (by omega)

theorem blt_true {a b : ℕ} (h : a < b) : Nat.blt a b = true := ble_true h

theorem blt_false {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := ble_false (by omega)

theorem ble_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := ⟨Nat.le_of_ble_eq_true, ble_true⟩

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := ⟨fun h => Nat.le_of_ble_eq_true h, blt_true⟩

theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin
  rcases Nat.lt_or_ge b a with h | h
  · rw [ble_false h, Bool.cond_false, min_eq_right h.le]
  · rw [ble_true h, Bool.cond_true, min_eq_left h]

theorem nmax_eq (a b : ℕ) : nmax a b = max a b := by
  unfold nmax
  rcases Nat.lt_or_ge b a with h | h
  · rw [ble_false h, Bool.cond_false, max_eq_left h.le]
  · rw [ble_true h, Bool.cond_true, max_eq_right h]

theorem bit_eq (M s : ℕ) : bit M s = M.testBit s := by
  unfold bit
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (M >>> s) with h | h <;> rw [h] <;> rfl

theorem testBit_bits (a b u : ℕ) : (bits a b).testBit u = decide (a ≤ u ∧ u ≤ b) := by
  unfold bits
  rcases Nat.lt_or_ge b a with h | h
  · rw [blt_true h, Bool.cond_true, Nat.zero_testBit]
    symm
    simp only [decide_eq_false_iff_not, not_and, not_le]
    omega
  · rw [blt_false h, Bool.cond_false, Nat.testBit_shiftLeft,
      Nat.testBit_two_pow_sub_one]
    by_cases hu : a ≤ u
    · simp only [ge_iff_le, hu, decide_true, Bool.true_and, true_and]
      congr 1
      exact propext ⟨fun h' => by omega, fun h' => by omega⟩
    · simp [hu]

/-! ### The subset sums of a box with deeper cells -/

/-- The lower sum of a box. -/
def loSum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: rest => p.1 + loSum rest

theorem zero_mem_subsetSums (zs : List (ℕ × ℕ)) : ((0 : ℕ), (0 : ℕ)) ∈ subsetSums zs := by
  induction zs with
  | nil => simp [subsetSums]
  | cons p rest ih => simp only [subsetSums, List.mem_append]; exact Or.inl ih

theorem full_mem_subsetSums (zs : List (ℕ × ℕ)) : (loSum zs, hiSum zs) ∈ subsetSums zs := by
  induction zs with
  | nil => simp [subsetSums, loSum, hiSum]
  | cons p rest ih =>
    simp only [subsetSums, List.mem_append, List.mem_map, loSum, hiSum]
    exact Or.inr ⟨_, ih, by simp [Nat.add_comm]⟩

/-- A subset sum of `ys` is one of `ys ++ zs`, alone and with all of `zs`. -/
theorem mem_subsetSums_append {ys zs : List (ℕ × ℕ)} {s : ℕ × ℕ} (hs : s ∈ subsetSums ys) :
    s ∈ subsetSums (ys ++ zs) ∧ (s.1 + loSum zs, s.2 + hiSum zs) ∈ subsetSums (ys ++ zs) := by
  induction ys generalizing s with
  | nil =>
    simp only [subsetSums, List.mem_singleton] at hs
    subst hs
    exact ⟨zero_mem_subsetSums zs, by simpa using full_mem_subsetSums zs⟩
  | cons p rest ih =>
    simp only [subsetSums, List.mem_append, List.mem_map, List.cons_append] at hs ⊢
    rcases hs with hs | ⟨s', hs', rfl⟩
    · exact ⟨Or.inl (ih hs).1, Or.inl (ih hs).2⟩
    · refine ⟨Or.inr ⟨s', (ih hs').1, rfl⟩, Or.inr ⟨_, (ih hs').2, ?_⟩⟩
      simp only [Prod.mk.injEq]
      constructor <;> ring

theorem hiSum_append (ys zs : List (ℕ × ℕ)) : hiSum (ys ++ zs) = hiSum ys + hiSum zs := by
  induction ys with
  | nil => simp [hiSum]
  | cons p rest ih => simp only [List.cons_append, hiSum, ih]; ring

theorem le_hiSum_of_mem {ys : List (ℕ × ℕ)} {s : ℕ × ℕ} (hs : s ∈ subsetSums ys) : s.2 ≤ hiSum ys := by
  induction ys generalizing s with
  | nil => simp only [subsetSums, List.mem_singleton] at hs; subst hs; simp [hiSum]
  | cons p rest ih =>
    simp only [subsetSums, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨s', hs', rfl⟩
    · have := ih hs; simp only [hiSum]; omega
    · have := ih hs'; simp only [hiSum]; omega

/-- A fold that keeps the least value of `f` over the entries that satisfy `P` ends at most at its start and at each
such entry's value. -/
theorem foldl_min_le {α : Type*} (P : α → Prop) [DecidablePred P] (f : α → ℕ) :
    ∀ (l : List α) (acc : Option ℕ),
      (∀ a, acc = some a → ∃ T, l.foldl (fun acc s => if P s then some (optMin acc (f s)) else acc) acc = some T ∧
        T ≤ a) ∧
      ∀ s ∈ l, P s → ∃ T, l.foldl (fun acc s => if P s then some (optMin acc (f s)) else acc) acc = some T ∧
        T ≤ f s := by
  intro l
  induction l with
  | nil => exact fun acc => ⟨fun a h => ⟨a, h, le_rfl⟩, fun s hs => absurd hs List.not_mem_nil⟩
  | cons x l ih =>
    intro acc
    have hstep : ∀ a, (if P x then some (optMin acc (f x)) else acc) = some a → ∃ T,
        (x :: l).foldl (fun acc s => if P s then some (optMin acc (f s)) else acc) acc = some T ∧ T ≤ a := by
      intro a ha
      obtain ⟨T, hT, hle⟩ := (ih _).1 a ha
      exact ⟨T, hT, hle⟩
    refine ⟨fun a ha => ?_, fun s hs hP => ?_⟩
    · by_cases hPx : P x
      · obtain ⟨T, hT, hle⟩ := hstep (optMin acc (f x)) (by rw [ite_eq_left hPx])
        refine ⟨T, hT, hle.trans ?_⟩
        rw [ha]
        exact min_le_left _ _
      · exact hstep a (by rw [ite_eq_right hPx, ha])
    · rcases List.mem_cons.1 hs with rfl | hs
      · obtain ⟨T, hT, hle⟩ := hstep (optMin acc (f s)) (by rw [ite_eq_left hP])
        refine ⟨T, hT, hle.trans ?_⟩
        cases acc with
        | none => exact le_rfl
        | some a => exact min_le_right _ _
      · exact (ih _).2 s hs hP

variable [Grid]

/-- `tstar` of a box is at most `cIB` at each of its subset sums whose upper end is below `DEN − U1`. -/
theorem tstar_le {xs : List (ℕ × ℕ)} {s : ℕ × ℕ} (hs : s ∈ subsetSums xs) (hlt : s.2 < DEN - U1) :
    ∃ T, tstar xs = some T ∧ T ≤ cIB s :=
  (foldl_min_le (fun s : ℕ × ℕ => s.2 < DEN - U1) cIB (subsetSums xs) none).2 s hs hlt

/-! ### The masks -/

/-- A coarse cell's lower end. -/
theorem eC_eq (c : ℕ) : eC c = V + HC * c := rfl

section Masks

omit [Grid] in
/-- A selection of a box's cells: its lower and upper sums are a subset sum. -/
theorem mem_subsetSums_sel {m : ℕ} (f : Fin m → ℕ × ℕ) (sel : Fin m → Bool) :
    (∑ t, cond (sel t) (f t).1 0, ∑ t, cond (sel t) (f t).2 0) ∈ subsetSums (List.ofFn f) := by
  induction m with
  | zero => simp [subsetSums]
  | succ m ih =>
    rw [List.ofFn_succ, subsetSums, List.mem_append, List.mem_map, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h := ih (fun t => f t.succ) (fun t => sel t.succ)
    cases hs : sel 0
    · left
      simpa [hs] using h
    · right
      exact ⟨_, h, by simp [Nat.add_comm]⟩

/-- A selection of a box's cells with its sums inside `U` makes the box surely evaluable. -/
theorem surelyEval_of_sel {m : ℕ} (f : Fin m → ℕ × ℕ) (sel : Fin m → Bool)
    (h : inside (∑ t, cond (sel t) (f t).1 0) (∑ t, cond (sel t) (f t).2 0) = true) :
    surelyEval (List.ofFn f) = true := by
  rw [surelyEval_eq]
  unfold surelyEvalSpec
  rw [List.any_eq_true]
  exact ⟨_, mem_subsetSums_sel f sel, h⟩

omit [Grid] in
/-- `above x y d ≤ t` only if `y + d·t` exceeds `x`. -/
theorem lt_of_above_le {x y d t : ℕ} (hd : 0 < d) (h : above x y d ≤ t) : x < y + d * t := by
  unfold above at h
  by_cases hy : y ≤ x
  · rw [ble_true hy, Bool.cond_true] at h
    have h' := (Nat.div_lt_iff_lt_mul hd).1 (show (x - y) / d < t by omega)
    rw [Nat.mul_comm] at h'
    omega
  · have : 0 ≤ d * t := Nat.zero_le _
    omega

/-- A bit `u` of `lbase1 m wl wh`: the box of `m + 1` cells with index sum `u` lies in `(wl, wh)`. -/
theorem lbase1_bit {m wl wh u : ℕ} (hH : 0 < H) (h : (lbase1 m wl wh).testBit u = true) :
    wl < (m + 1) * V + H * u ∧ (m + 1) * V + H * u + (m + 1) * H < wh := by
  unfold lbase1 at h
  by_cases hw : (m + 1) * (V + H) < wh
  · rw [blt_true hw, Bool.cond_true, testBit_bits, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨lt_of_above_le hH h1, ?_⟩
    have h3 := (Nat.le_div_iff_mul_le hH).1 h2
    have hA : (m + 1) * (V + H) = (m + 1) * V + (m + 1) * H := by ring
    rw [Nat.mul_comm] at h3
    omega
  · rw [blt_false (not_lt.1 hw), Bool.cond_false, Nat.zero_testBit] at h
    exact absurd h (by simp)

/-- A bit `u` of `lbase m`: the box of `m + 1` cells with index sum `u` lies inside `U`. -/
theorem lbase_bit {m u : ℕ} (hH : 0 < H) (h : (lbase m).testBit u = true) :
    inside ((m + 1) * V + H * u) ((m + 1) * V + H * u + (m + 1) * H) = true := by
  unfold lbase at h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  unfold inside
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with h | h
  · exact Or.inl (lbase1_bit hH h)
  · exact Or.inr (lbase1_bit hH h)

/-- A bit `t` of `sbase1 mr m ρ wl wh`: the box with `mr` cells of index sum `ρ + 4t'` and `m` coarse cells of index
sum `t − t'` lies in `(wl, wh)`. -/
theorem sbase1_bit {mr m ρ wl wh t : ℕ} (hHC : 0 < HC) (h : (sbase1 mr m ρ wl wh).testBit t = true) :
    wl < (mr + m) * V + H * ρ + HC * t ∧ (mr + m) * V + H * ρ + mr * H + m * HC + HC * t < wh := by
  unfold sbase1 at h
  by_cases hw : (mr + m) * V + H * ρ + mr * H + m * HC < wh
  · rw [blt_true hw, Bool.cond_true, testBit_bits, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨lt_of_above_le hHC h1, ?_⟩
    have h3 := (Nat.le_div_iff_mul_le hHC).1 h2
    rw [Nat.mul_comm] at h3
    omega
  · rw [blt_false (not_lt.1 hw), Bool.cond_false, Nat.zero_testBit] at h
    exact absurd h (by simp)

theorem sbase_bit {mr m ρ t : ℕ} (hHC : 0 < HC) (h : (sbase mr m ρ).testBit t = true) :
    inside ((mr + m) * V + H * ρ + HC * t) ((mr + m) * V + H * ρ + mr * H + m * HC + HC * t) = true := by
  unfold sbase at h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  unfold inside
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with h | h
  · exact Or.inl (sbase1_bit hHC h)
  · exact Or.inr (sbase1_bit hHC h)

/-- A bit `t` of `smask mr m N`, for `HC = 4H`: the box of `mr` cells with index sum `N` and `m` coarse cells with
index sum `t` lies inside `U`. -/
theorem smask_bit {mr m N t : ℕ} (hHC : HC = 4 * H) (hH : 0 < H) (h : (smask mr m N).testBit t = true) :
    inside (mr * V + H * N + m * V + HC * t) (mr * V + H * N + mr * H + m * V + m * HC + HC * t) = true := by
  unfold smask at h
  rw [lit_eq, Nat.testBit_shiftRight] at h
  have h' := sbase_bit (by omega) h
  have hN : H * N = H * (N % 4) + HC * (N / 4) := by
    calc H * N = H * (N % 4 + 4 * (N / 4)) := by rw [Nat.mod_add_div]
      _ = H * (N % 4) + HC * (N / 4) := by rw [hHC]; ring
  have e1 : mr * V + H * N + m * V + HC * t = (mr + m) * V + H * (N % 4) + HC * (N / 4 + t) := by
    rw [hN]; ring
  have e2 : mr * V + H * N + mr * H + m * V + m * HC + HC * t =
      (mr + m) * V + H * (N % 4) + mr * H + m * HC + HC * (N / 4 + t) := by
    rw [hN]; ring
  rw [e1, e2]
  exact h'

/-- The lower sum of a selection of the cells `(i, j, k)`. -/
def lo3 (i j k : ℕ) (sel : Fin 3 → Bool) : ℕ :=
  cond (sel 0) (SieveCert.e i) 0 + cond (sel 1) (SieveCert.e j) 0 + cond (sel 2) (SieveCert.e k) 0

/-- The lower sum of a selection of the cells `(i, j, k, l)`. -/
def lo4 (i j k l : ℕ) (sel : Fin 4 → Bool) : ℕ :=
  cond (sel 0) (SieveCert.e i) 0 + cond (sel 1) (SieveCert.e j) 0 + cond (sel 2) (SieveCert.e k) 0 +
    cond (sel 3) (SieveCert.e l) 0

/-- The upper sum of a selection of the cells `(i, j, k)`. -/
def hi3s (i j k : ℕ) (sel : Fin 3 → Bool) : ℕ :=
  cond (sel 0) (SieveCert.e i + H) 0 + cond (sel 1) (SieveCert.e j + H) 0 + cond (sel 2) (SieveCert.e k + H) 0

/-- The upper sum of a selection of the cells `(i, j, k, l)`. -/
def hi4s (i j k l : ℕ) (sel : Fin 4 → Bool) : ℕ :=
  cond (sel 0) (SieveCert.e i + H) 0 + cond (sel 1) (SieveCert.e j + H) 0 + cond (sel 2) (SieveCert.e k + H) 0 +
    cond (sel 3) (SieveCert.e l + H) 0

/-- **The mask of `l`**: a bit `l` of `lmask i j k` gives a selection of `(i, j, k)` whose sums with the cell `l` lie
inside `U`. -/
theorem lmask_sel {i j k l : ℕ} (hH : 0 < H) (h : (lmask i j k).testBit l = true) :
    ∃ sel : Fin 3 → Bool, inside (lo3 i j k sel + SieveCert.e l) (hi3s i j k sel + (SieveCert.e l + H)) = true := by
  unfold lmask at h
  simp only [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftRight, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h <;> have h' := lbase_bit hH h
  · refine ⟨![false, false, false], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e]
  · refine ⟨![true, false, false], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring
  · refine ⟨![false, true, false], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring
  · refine ⟨![false, false, true], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring
  · refine ⟨![true, true, false], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring
  · refine ⟨![true, false, true], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring
  · refine ⟨![false, true, true], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring
  · refine ⟨![true, true, true], ?_⟩
    convert h' using 2 <;> simp [lo3, hi3s, SieveCert.e] <;> ring


/-- **The coarse masks**, for `HC = 4H`: a bit `t` of `emask m i j k l` gives a selection of `(i, j, k, l)` whose sums
with `m` coarse cells of index sum `t` lie inside `U`. -/
theorem emask_sel {m i j k l t : ℕ} (hHC : HC = 4 * H) (hH : 0 < H) (h : (emask m i j k l).testBit t = true) :
    ∃ sel : Fin 4 → Bool, inside (lo4 i j k l sel + m * V + HC * t) (hi4s i j k l sel + m * V + m * HC + HC * t) =
      true := by
  have hl : H * l = H * (l % 4) + HC * (l / 4) := by
    calc H * l = H * (l % 4 + 4 * (l / 4)) := by rw [Nat.mod_add_div]
      _ = H * (l % 4) + HC * (l / 4) := by rw [hHC]; ring
  unfold emask at h
  rw [lit_eq] at h
  unfold emask3 fmask3 at h
  simp only [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftRight, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> have h' := smask_bit hHC hH h
  · refine ⟨![false, false, false, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e]
  · refine ⟨![true, false, false, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e]
  · refine ⟨![false, true, false, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e]
  · refine ⟨![false, false, true, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e]
  · refine ⟨![true, true, false, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![true, false, true, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![false, true, true, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![true, true, true, false], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![false, false, false, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![true, false, false, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![false, true, false, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![false, false, true, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![true, true, false, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![true, false, true, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![false, true, true, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]
  · refine ⟨![true, true, true, true], ?_⟩
    convert h' using 2 <;> simp [lo4, hi4s, SieveCert.e] <;> linarith [hl]


/-- **A bit of the mask of `l` makes the box `(i, j, k, l)` surely evaluable.** -/
theorem surelyEval4_of_lmask {i j k l : ℕ} (hH : 0 < H) (h : (lmask i j k).testBit l = true) :
    surelyEval [cell i, cell j, cell k, cell l] = true := by
  obtain ⟨sel, hin⟩ := lmask_sel hH h
  have e1 : ∑ t : Fin 4, cond (![sel 0, sel 1, sel 2, true] t) (![cell i, cell j, cell k, cell l] t).1 0 =
      lo3 i j k sel + SieveCert.e l := by rw [Fin.sum_univ_four]; rfl
  have e2 : ∑ t : Fin 4, cond (![sel 0, sel 1, sel 2, true] t) (![cell i, cell j, cell k, cell l] t).2 0 =
      hi3s i j k sel + (SieveCert.e l + H) := by rw [Fin.sum_univ_four]; rfl
  have h4 := surelyEval_of_sel ![cell i, cell j, cell k, cell l] ![sel 0, sel 1, sel 2, true] (by
    rw [e1, e2]; exact hin)
  simpa [List.ofFn_succ] using h4

/-- **A bit `b` of the coarse mask of one cell makes the box `(i, j, k, l, b)` surely evaluable**, for `HC = 4H`. -/
theorem surelyEval5_of_emask {i j k l b : ℕ} (hHC : HC = 4 * H) (hH : 0 < H)
    (h : (emask 1 i j k l).testBit b = true) :
    surelyEval [cell i, cell j, cell k, cell l, cellC b] = true := by
  obtain ⟨sel, hin⟩ := emask_sel hHC hH h
  have e1 : ∑ t : Fin 5, cond (![sel 0, sel 1, sel 2, sel 3, true] t)
      (![cell i, cell j, cell k, cell l, cellC b] t).1 0 = lo4 i j k l sel + eC b := by rw [Fin.sum_univ_five]; rfl
  have e2 : ∑ t : Fin 5, cond (![sel 0, sel 1, sel 2, sel 3, true] t)
      (![cell i, cell j, cell k, cell l, cellC b] t).2 0 = hi4s i j k l sel + (eC b + HC) := by
    rw [Fin.sum_univ_five]; rfl
  have h5 := surelyEval_of_sel ![cell i, cell j, cell k, cell l, cellC b] ![sel 0, sel 1, sel 2, sel 3, true] (by
    rw [e1, e2]
    convert hin using 2 <;> rw [eC_eq] <;> ring)
  simpa [List.ofFn_succ] using h5

/-- **A bit `c` of the coarse mask of one cell, or `b + c` of that of two, makes the box `(i, j, k, l, b, c)` surely
evaluable**, for `HC = 4H`. -/
theorem surelyEval6_of_emask {i j k l b c : ℕ} (hHC : HC = 4 * H) (hH : 0 < H)
    (h : (emask 1 i j k l).testBit c = true ∨ (emask 2 i j k l).testBit (b + c) = true) :
    surelyEval [cell i, cell j, cell k, cell l, cellC b, cellC c] = true := by
  rcases h with h | h
  · obtain ⟨sel, hin⟩ := emask_sel hHC hH h
    have e1 : ∑ t : Fin 6, cond (![sel 0, sel 1, sel 2, sel 3, false, true] t)
        (![cell i, cell j, cell k, cell l, cellC b, cellC c] t).1 0 = lo4 i j k l sel + eC c := by
      rw [Fin.sum_univ_six]; rfl
    have e2 : ∑ t : Fin 6, cond (![sel 0, sel 1, sel 2, sel 3, false, true] t)
        (![cell i, cell j, cell k, cell l, cellC b, cellC c] t).2 0 = hi4s i j k l sel + (eC c + HC) := by
      rw [Fin.sum_univ_six]; rfl
    have h6 := surelyEval_of_sel ![cell i, cell j, cell k, cell l, cellC b, cellC c]
      ![sel 0, sel 1, sel 2, sel 3, false, true] (by
        rw [e1, e2]
        convert hin using 2 <;> rw [eC_eq] <;> ring)
    simpa [List.ofFn_succ] using h6
  · obtain ⟨sel, hin⟩ := emask_sel hHC hH h
    have e1 : ∑ t : Fin 6, cond (![sel 0, sel 1, sel 2, sel 3, true, true] t)
        (![cell i, cell j, cell k, cell l, cellC b, cellC c] t).1 0 = lo4 i j k l sel + eC b + eC c := by
      rw [Fin.sum_univ_six]; rfl
    have e2 : ∑ t : Fin 6, cond (![sel 0, sel 1, sel 2, sel 3, true, true] t)
        (![cell i, cell j, cell k, cell l, cellC b, cellC c] t).2 0 = hi4s i j k l sel + (eC b + HC) + (eC c + HC) := by
      rw [Fin.sum_univ_six]; rfl
    have h6 := surelyEval_of_sel ![cell i, cell j, cell k, cell l, cellC b, cellC c]
      ![sel 0, sel 1, sel 2, sel 3, true, true] (by
        rw [e1, e2]
        convert hin using 2 <;> rw [eC_eq, eC_eq] <;> ring)
    simpa [List.ofFn_succ] using h6

end Masks

variable [IBPar]

omit [Grid] in
/-- The estimate holds at smaller sums. -/
theorem condIB_mono {a₁ a₂ b₁ b₂ : ℕ} (h : condIB a₁ a₂ = true) (h₁ : b₁ ≤ a₁) (h₂ : b₂ ≤ a₂) :
    condIB b₁ b₂ = true := by
  simp only [condIB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨lt_of_le_of_lt (Nat.mul_le_mul_right _ h₁) h.1, by omega⟩

/-- **A split of a box with deeper cells.** For boxes `ys` and `zs` with `tstar ys = some T` and a subset sum `s` of
`ys`, if the estimate holds at the split of `ys ++ zs` into `s` and the rest with `e` (of exponent `T`) on either side
and `zs` on either side, `ibOK` passes `ys ++ zs`. -/
theorem ibOK_append {ys zs : List (ℕ × ℕ)} {T : ℕ} (hT : tstar ys = some T) {s : ℕ × ℕ} (hs : s ∈ subsetSums ys)
    (h : condIB (s.2 + T + hiSum zs) (hiSum ys - s.2) = true ∨
      condIB (s.2 + T) (hiSum ys - s.2 + hiSum zs) = true ∨
      condIB (s.2 + hiSum zs) (hiSum ys - s.2 + T) = true ∨
      condIB s.2 (hiSum ys - s.2 + T + hiSum zs) = true) :
    ibOK (ys ++ zs) = true := by
  obtain ⟨s₀, hs₀, hlt, hc⟩ := tstar_mem hT
  obtain ⟨T', hT', hle⟩ := tstar_le (mem_subsetSums_append (zs := zs) hs₀).1 hlt
  rw [hc] at hle
  have hsle := le_hiSum_of_mem hs
  have hsum := hiSum_append ys zs
  obtain ⟨hs1, hs2⟩ := mem_subsetSums_append (zs := zs) hs
  unfold ibOK
  rw [hT']
  simp only [leafIB, List.any_eq_true, Bool.or_eq_true]
  rcases h with h | h | h | h
  · refine ⟨_, hs2, Or.inl (condIB_mono h (by omega) (by omega))⟩
  · refine ⟨_, hs1, Or.inl (condIB_mono h (by omega) (by omega))⟩
  · refine ⟨_, hs2, Or.inr (condIB_mono h (by omega) (by omega))⟩
  · refine ⟨_, hs1, Or.inr (condIB_mono h (by omega) (by omega))⟩

/-! ### The block test -/

omit [Grid] in
theorem dcpT_sound {a₁ a₂ D : ℕ} (h : D < dcpT a₁ a₂) : condIB (a₁ + D) a₂ = true := by
  unfold dcpT at h
  rw [nmin_eq, lt_min_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only [condIB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · by_cases hc : a₁ * IBPar.Lnum < (IBPar.Lnum - IBPar.Lden) * DEN
    · rw [blt_true hc,
        Bool.cond_true] at h1
      have hL : 0 < IBPar.Lnum := by
        rcases Nat.eq_zero_or_pos IBPar.Lnum with h0 | h0
        · rw [h0] at hc; simp at hc
        · exact h0
      have hD : D ≤ ((IBPar.Lnum - IBPar.Lden) * DEN - a₁ * IBPar.Lnum - 1) / IBPar.Lnum := by omega
      have := (Nat.le_div_iff_mul_le hL).1 hD
      rw [Nat.add_mul]
      omega
    · rw [blt_false (not_lt.1 hc),
        Bool.cond_false] at h1
      omega
  · by_cases hc : a₁ + 2 * a₂ < DEN
    · rw [blt_true hc, Bool.cond_true] at h2
      omega
    · rw [blt_false (not_lt.1 hc), Bool.cond_false] at h2
      omega

omit [Grid] in
theorem dcpF_sound {a₁ a₂ D : ℕ} (h : D < dcpF a₁ a₂) : condIB a₁ (a₂ + D) = true := by
  unfold dcpF at h
  simp only [condIB, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hc : a₁ * IBPar.Lnum < (IBPar.Lnum - IBPar.Lden) * DEN
  · rw [blt_true hc,
      Bool.cond_true] at h
    refine ⟨hc, ?_⟩
    by_cases hc2 : a₁ + 2 * a₂ < DEN
    · rw [blt_true hc2, Bool.cond_true] at h
      have hD : D ≤ (DEN - a₁ - 2 * a₂ - 1) / 2 := by omega
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hD
      omega
    · rw [blt_false (not_lt.1 hc2), Bool.cond_false] at h
      omega
  · rw [blt_false (not_lt.1 hc),
      Bool.cond_false] at h
    omega

omit [Grid] in
theorem dcp_sound {a₁ a₂ D : ℕ} (h : D < dcp a₁ a₂) : condIB (a₁ + D) a₂ = true ∨ condIB a₁ (a₂ + D) = true := by
  unfold dcp at h
  rw [nmax_eq, lt_max_iff] at h
  exact h.imp dcpT_sound dcpF_sound

omit [Grid] [IBPar] in
/-- A fold that keeps the largest value of `g` exceeds `D` only at its start or at an entry where `g` does. -/
theorem foldl_nmax_lt {α : Type*} (g : α → ℕ) (D : ℕ) :
    ∀ (l : List α) (a : ℕ), D < l.foldl (fun acc s => nmax acc (g s)) a → D < a ∨ ∃ s ∈ l, D < g s := by
  intro l
  induction l with
  | nil => exact fun a h => Or.inl h
  | cons x l ih =>
    intro a h
    rcases ih _ h with h' | ⟨s, hs, hlt⟩
    · change D < nmax a (g x) at h'
      rw [nmax_eq, lt_max_iff] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨x, List.mem_cons_self, h'⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hlt⟩

omit [Grid] in
/-- **`dmaxL` is sound**: below it, a split of the box `xs` satisfies the estimate with any deeper cells of upper sum
`D` on one side. -/
theorem dmaxL_sound {xs : List (ℕ × ℕ)} {T D : ℕ} (h : D < dmaxL xs T) :
    ∃ s ∈ subsetSums xs,
      (condIB (s.2 + T + D) (hiSum xs - s.2) = true ∨ condIB (s.2 + T) (hiSum xs - s.2 + D) = true ∨
        condIB (s.2 + D) (hiSum xs - s.2 + T) = true ∨ condIB s.2 (hiSum xs - s.2 + T + D) = true) := by
  unfold dmaxL at h
  rcases foldl_nmax_lt (fun s : ℕ × ℕ => nmax (dcp (s.2 + T) (hiSum xs - s.2)) (dcp s.2 (hiSum xs - s.2 + T))) D
    (subsetSums xs) 0 h with h0 | ⟨s, hs, hlt⟩
  · exact absurd h0 (Nat.not_lt_zero _)
  refine ⟨s, hs, ?_⟩
  have hlt' : D < nmax (dcp (s.2 + T) (hiSum xs - s.2)) (dcp s.2 (hiSum xs - s.2 + T)) := hlt
  rw [nmax_eq, lt_max_iff] at hlt'
  rcases hlt' with hlt' | hlt'
  · rcases dcp_sound hlt' with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases dcp_sound hlt' with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

/-- **`dmax3` is sound**: below it, a split of the box `(i, j, k)` satisfies the estimate with any deeper cells of
upper sum `D` on one side. -/
theorem dmax3_sound {i j k D : ℕ} (h : D < dmax3 i j k) : ∃ T, tstar [cell i, cell j, cell k] = some T ∧
    ∃ s ∈ subsetSums [cell i, cell j, cell k],
      (condIB (s.2 + T + D) (hiSum [cell i, cell j, cell k] - s.2) = true ∨
        condIB (s.2 + T) (hiSum [cell i, cell j, cell k] - s.2 + D) = true ∨
        condIB (s.2 + D) (hiSum [cell i, cell j, cell k] - s.2 + T) = true ∨
        condIB s.2 (hiSum [cell i, cell j, cell k] - s.2 + T + D) = true) := by
  unfold dmax3 at h
  rcases ht : tstar [cell i, cell j, cell k] with _ | T
  · rw [ht] at h; exact absurd h (Nat.not_lt_zero _)
  rw [ht] at h
  exact ⟨T, rfl, dmaxL_sound h⟩

omit [IBPar] in
theorem hiSum_cells3 (i j k : ℕ) :
    hiSum [cell i, cell j, cell k] = SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H := by
  simp only [hiSum, cell]
  ring

/-- **The block test is sound.** A box `(i, j, k) ++ zs` that passes `okD`, with the deeper sum `D` the upper sum of
`zs` and `h` the box's last upper end, passes the bilinear rule. -/
theorem okIB_of_okD {i j k : ℕ} (zs : List (ℕ × ℕ))
    (h : okD (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k) (hiSum zs)
      (lastHi ([cell i, cell j, cell k] ++ zs)) = true) :
    okIB ([cell i, cell j, cell k] ++ zs) = true := by
  have hsum : hiSum ([cell i, cell j, cell k] ++ zs) =
      SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H + hiSum zs := by
    rw [hiSum_append, hiSum_cells3]
  unfold okD at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  unfold okIB limOK nbOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hsum]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, h1⟩
    obtain ⟨T, hT, s, hs, hc⟩ := dmax3_sound h2
    exact ibOK_append hT hs hc


/-! ### The tests of the deeper boxes -/

omit [IBPar] in
/-- `okD` passes a smaller deeper sum and last upper end. -/
theorem okD_mono {hi3 Dm D h D' h' : ℕ} (hok : okD hi3 Dm D h = true) (hD : D' ≤ D) (hh : h' ≤ h) :
    okD hi3 Dm D' h' = true := by
  unfold okD at hok ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hok ⊢
  omega


omit [IBPar] in
theorem lt_cntH {X c : ℕ} (hHC : 0 < HC) (h : c < cntH X) : V + HC * (c + 1) ≤ X := by
  unfold cntH at h
  by_cases hX : V + HC ≤ X
  · rw [ble_true hX, Bool.cond_true] at h
    have := (Nat.le_div_iff_mul_le hHC).1 (show c + 1 ≤ (X - V) / HC by omega)
    rw [Nat.mul_comm] at this
    omega
  · rw [ble_false (not_le.1 hX), Bool.cond_false] at h
    omega

omit [IBPar] in
/-- **`cstar` is sound**: for `c < cstar`, the worst box of depth 7 below `(…, b)`, with the deeper sum
`hl + hb + 2(eC c + HC)` and last upper end `eC c + HC`, passes `okD`. -/
theorem cstar_sound {hi3 Dm hl hb c : ℕ} (hHC : 0 < HC) (h : c < cstar hi3 Dm hl hb) :
    okD hi3 Dm (hl + hb + 2 * (eC c + HC)) (eC c + HC) = true := by
  unfold cstar at h
  rw [nmax_eq, nmin_eq, lt_max_iff, lt_min_iff] at h
  unfold okD
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq]
  have hc : eC c + HC = V + HC * (c + 1) := by rw [eC_eq]; ring
  rw [hc]
  rcases h with h | ⟨h1, h2⟩
  · by_cases ht : hi3 + hl + hb < lim
    · rw [blt_true ht, Bool.cond_true] at h
      have := lt_cntH hHC h
      have := Nat.mul_div_le (lim - hi3 - hl - hb - 1) 2
      omega
    · rw [blt_false (not_lt.1 ht), Bool.cond_false] at h
      omega
  · refine Or.inr ⟨?_, ?_⟩
    · by_cases ht : hi3 + hl + hb < DEN
      · rw [blt_true ht, Bool.cond_true] at h1
        have := lt_cntH hHC h1
        have := Nat.mul_div_le (DEN - hi3 - hl - hb - 1) 3
        omega
      · rw [blt_false (not_lt.1 ht), Bool.cond_false] at h1
        omega
    · by_cases ht : hl + hb < Dm
      · rw [blt_true ht, Bool.cond_true] at h2
        have := lt_cntH hHC h2
        have := Nat.mul_div_le (Dm - hl - hb - 1) 2
        omega
      · rw [blt_false (not_lt.1 ht), Bool.cond_false] at h2
        omega

end SieveDeep

namespace SieveDeep

open SieveCert

/-! ### The regions in closed form -/

section Regions

variable [Grid]

/-- A cell's lower end. -/
theorem e_eq (l : ℕ) : SieveCert.e l = V + H * l := rfl

theorem lt_creg_iff {S c : ℕ} (hHC : 0 < HC) : c < creg S ↔ S + 2 * eC c ≤ DEN := by
  unfold creg
  rw [eC_eq]
  have e2 : 2 * (V + HC * c) = 2 * V + c * (2 * HC) := by ring
  rw [e2]
  by_cases h : S + 2 * V ≤ DEN
  · rw [ble_true h, Bool.cond_true]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
    omega
  · rw [ble_false (not_le.1 h), Bool.cond_false]
    omega

theorem lt_lreg_iff {S l : ℕ} (hH : 0 < H) : l < lreg S ↔ S + 2 * SieveCert.e l ≤ DEN := by
  unfold lreg
  rw [e_eq]
  have e2 : 2 * (V + H * l) = 2 * V + l * (2 * H) := by ring
  rw [e2]
  by_cases h : S + 2 * V ≤ DEN
  · rw [ble_true h, Bool.cond_true]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
    omega
  · rw [ble_false (not_le.1 h), Bool.cond_false]
    omega

/-- The region's coarse cells `b` below the cell `l`, for `HC = 4H`. -/
theorem lt_bcnt_iff {I4 l b : ℕ} (hHC : HC = 4 * H) (hH : 0 < H) :
    b < bcnt I4 l ↔ 4 * b ≤ l ∧ 4 * V + H * I4 + 2 * eC b ≤ DEN := by
  unfold bcnt
  rw [nmin_eq, lt_min_iff, lt_creg_iff (by omega), Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by norm_num), Nat.mul_comm]

/-- `inKK5` is the region of `bcnt`, for `HC = 4H`. -/
theorem inKK5_iff {i j k l b : ℕ} (hHC : HC = 4 * H) (hH : 0 < H) :
    inKK5 i j k l b = true ↔ b < bcnt (i + j + k + l) l := by
  rw [lt_bcnt_iff hHC hH]
  unfold inKK5
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have e1 : SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l = 4 * V + H * (i + j + k + l) := by
    simp only [e_eq]; ring
  rw [e1]
  refine and_congr_left fun _ => ?_
  rw [eC_eq, e_eq, hHC]
  constructor
  · intro h
    have : H * (4 * b) < H * (l + 1) := by nlinarith
    have := (Nat.mul_lt_mul_left hH).1 this
    omega
  · intro h
    have : H * (4 * b) ≤ H * l := Nat.mul_le_mul_left _ h
    nlinarith

end Regions

/-! ### The certificate's decisions -/

section Scheme

variable [Grid] [IBPar]

/-- The upper sum of the box `(i, j, k)`. -/
def hi3 (i j k : ℕ) : ℕ := SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H

/-- **The certificate's decision at depth 4**: `cost4` takes the cell's cells of depths 5 and 6. Its box passes `okD`,
and either every box below passes (`pureOK`) and `Fpure` is cheaper than the cell's bound, or the boxes of depth 5 that
the mask leaves pass (`bad5 = 0`) and `cost6` is cheaper. -/
def dec4D (i j k l : ℕ) : Bool :=
  okD (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (SieveCert.e l + H) &&
    cond (pureOK (hi3 i j k) (dmax3 i j k) (i + j + k + l) l)
      (Nat.blt (trapF (SieveCert.e l) H * Fpure (i + j + k + l) l) (Q4 (i + j + k) l * SC ^ 4))
      (Nat.beq (bad5 (hi3 i j k) (dmax3 i j k) (i + j + k + l) l (emask 1 i j k l)) 0 &&
        Nat.blt (trapF (SieveCert.e l) H *
          cost6 (hi3 i j k) (dmax3 i j k) (i + j + k + l) l (emask 1 i j k l) (emask 2 i j k l))
          (Q4 (i + j + k) l * SC ^ 4))

/-- **The certificate's decision at depth 6**: the cell `c` below `(i, j, k, l, b)` lies in the prefix whose worst box
of depth 7 passes `okD` (`cstar`), and its cells of depths 7 and 8 are cheaper than its bound. -/
def dec6D (i j k l b c : ℕ) : Bool :=
  Nat.blt c (cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC)) &&
    Nat.blt (trapF (eC c) HC * R8 (i + j + k + l + 4 * b + 4 * c) c) (q6 (i + j + k + l + 4 * b) c * SC * SC)

/-- The decision at depth 2 passes the rule on the box `(i, j)` and on the boxes of its counted rows. -/
theorem allowedR_of_decD {i j : ℕ} (h : decD i j = true) : @allowedR _ ibRule i j = true := by
  unfold decD allowedD at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  unfold allowedR
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨h.1.1, fun k hk => ?_⟩
  rcases h.1.2 k hk with h' | h'
  · exact Or.inl h'
  · right
    exact okIB_of_okD (i := i) (j := j) (k := k) [] (by simpa [ok3D, hiSum, lastHi, cell] using h')

/-- The decision at depth 4 passes the rule on the box `(i, j, k, l)` and on the boxes of its counted cells of
depth 5, for `HC = 4H`. -/
theorem allowed4R_of_dec4D (hHC : HC = 4 * H) (hH : 0 < H) {i j k l : ℕ} (h : dec4D i j k l = true) :
    @allowed4R _ ibRule i j k l = true := by
  unfold dec4D at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h4, hrest⟩ := h
  unfold allowed4R
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨okIB_of_okD (i := i) (j := j) (k := k) [cell l] (by simpa [hi3, hiSum, lastHi, cell] using h4),
    fun b hb => ?_⟩
  by_cases hK : inKK5 i j k l b = true ∧ ne5 i j k l b = true
  · right
    have hb' : b < bcnt (i + j + k + l) l := (inKK5_iff hHC hH).1 hK.1
    have h5 : okD (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H + (eC b + HC)) (eC b + HC) = true := by
      cases hp : pureOK (hi3 i j k) (dmax3 i j k) (i + j + k + l) l
      · rw [hp, Bool.cond_false, Bool.and_eq_true] at hrest
        have h0 := Nat.eq_of_beq_eq_true hrest.1
        rw [bad5, sumTo_eq, Finset.sum_eq_zero_iff] at h0
        have hb0 := h0 b (Finset.mem_range.2 hb')
        have hnb : bit (emask 1 i j k l) b = false := by
          rw [bit_eq]
          by_contra hc
          have := surelyEval5_of_emask hHC hH (by simpa using hc)
          simp only [ne5, this, Bool.not_true] at hK
          exact absurd hK.2 (by simp)
        rw [hnb] at hb0
        cases hok : okD (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H + eC b + HC) (eC b + HC)
        · rw [hok] at hb0; simp at hb0
        · exact okD_mono hok (by omega) le_rfl
      · unfold pureOK at hp
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
        obtain ⟨⟨hbc, hm⟩, -⟩ := hp
        have hbc' : bcnt (i + j + k + l) l ≠ 0 := Nat.ne_of_beq_eq_false hbc
        have hle : eC b ≤ eC (bcnt (i + j + k + l) l - 1) := by
          rw [eC_eq, eC_eq]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
        exact okD_mono hm (by omega) (by omega)
    exact okIB_of_okD (i := i) (j := j) (k := k) [cell l, cellC b]
      (by simpa [hi3, hiSum, lastHi, cell, cellC, Nat.add_assoc] using h5)
  · left
    revert hK
    cases inKK5 i j k l b <;> cases ne5 i j k l b <;> simp

/-- The decision at depth 6 passes the rule on the box `(i, j, k, l, b, c)` and on the boxes of depth 7 of its
region, for `HC = 4H`. -/
theorem allowed6R_of_dec6D (hHC : HC = 4 * H) (hH : 0 < H) {i j k l b c : ℕ} (h : dec6D i j k l b c = true) :
    @SieveBuch.allowed6R _ ibRule i j k l b c = true := by
  unfold dec6D at h
  rw [Bool.and_eq_true, blt_iff] at h
  have hc7 : okD (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k)
      (SieveCert.e l + H + (eC b + HC) + 2 * (eC c + HC)) (eC c + HC) = true := cstar_sound (by omega : 0 < HC) h.1
  unfold SieveBuch.allowed6R
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨okIB_of_okD (i := i) (j := j) (k := k) [cell l, cellC b, cellC c]
    (okD_mono hc7 (by simp only [hiSum, cell, cellC]; omega) (by simp [lastHi, cellC])), fun d hd => ?_⟩
  by_cases hK : SieveBuch.inKK7 i j k l b c d = true
  · right
    have hdc : eC d ≤ eC c := by
      unfold SieveBuch.inKK7 at hK
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hK
      have h1 := hK.1
      rw [eC_eq, eC_eq] at h1 ⊢
      have : HC * d < HC * (c + 1) := by nlinarith
      have := (Nat.mul_lt_mul_left (by omega : 0 < HC)).1 this
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    exact okIB_of_okD (i := i) (j := j) (k := k) [cell l, cellC b, cellC c, cellC d]
      (okD_mono hc7 (by simp only [hiSum, cell, cellC]; omega)
        (by simp only [lastHi, cellC, List.cons_append, List.nil_append]; omega))
  · left
    simpa using hK

/-- **The certificate's scheme of decisions** under the bilinear rule, for `HC = 4H`: `decD`, `dec4D` and `dec6D`. -/
@[instance_reducible] def scheme (hHC : HC = 4 * H) (hH : 0 < H) : @SieveBuch.Scheme8 _ ibRule :=
  @SieveBuch.Scheme8.mk _ ibRule decD dec4D dec6D allowedR_of_decD (allowed4R_of_dec4D hHC hH)
    (allowed6R_of_dec6D hHC hH)

end Scheme

end SieveDeep
