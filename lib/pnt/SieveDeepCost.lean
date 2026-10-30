/-
# The certificate to depth 8: its costs bound the dropped cells' charges

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The definitions are `SieveDeepDefs.lean`'s, the decisions `SieveDeep.lean`'s (`decD`, `dec4D`,
`dec6D`), on a grid with `HC = 4H` (`hHC`) and `H > 0`.

* `Ch8` … `Ch3`: **the charges** of the cells that the decomposition to depth 8 drops below a decomposed cell `(i, j)`,
  in the shape of its dropped terms (`SieveBuch.Par.E8` … `E3`), each cell at the product of its primes' factors in
  fixed point: `trapF` for each prime but the last, `lastF` for the last, and `omKw`; `P3`, the factors of `(i, j, k)`,
  stays outside `Ch4`.
* `Ch8_eq`, `Ch7_eq`: below a cell of depth 7 the charges are `R8in`, and below a decomposed cell of depth 6 `R8`.
* `Ch6_le`: below `(i, j, k, l, b)`, the charges are at most the cost of the prefix `c < cs` at `vR` and of the rest
  at the bounds `q6` that the masks leave, when the prefix is that of `cstar`.
* `Ch5_le_Fpure`, `Ch5_le_cost6`, `Ch4_le_row`: the charges below a decomposed cell of depth 4 are at most its cost
  (`Fpure` when every box below passes, `cost6` otherwise), and the charges of a row are at most `row`.
* `Ch3_le`: **the charges below a cell `(i, j)` are at most `SC⁸·refcost`.**

The file imports `SieveDeep.lean`.
-/
import SieveDeep

namespace SieveDeep

open SieveCert Finset

/-! ### Sums with tests -/

/-- A sum over `s` with a test is at most a sum over `t` that holds each tested index with a larger term. -/
theorem sum_ite_le_sum {s t : Finset ℕ} {P : ℕ → Prop} [DecidablePred P] {f g : ℕ → ℕ}
    (h : ∀ c ∈ s, P c → c ∈ t ∧ f c ≤ g c) :
    ∑ c ∈ s, (if P c then f c else 0) ≤ ∑ c ∈ t, g c := by
  rw [← Finset.sum_filter]
  calc ∑ c ∈ s.filter P, f c ≤ ∑ c ∈ s.filter P, g c :=
        Finset.sum_le_sum fun c hc => (h c (Finset.mem_filter.1 hc).1 (Finset.mem_filter.1 hc).2).2
    _ ≤ ∑ c ∈ t, g c := Finset.sum_le_sum_of_subset_of_nonneg
        (fun c hc => (h c (Finset.mem_filter.1 hc).1 (Finset.mem_filter.1 hc).2).1) (fun _ _ _ => Nat.zero_le _)

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hc) h

theorem cond_ble (a b x : ℕ) : cond (Nat.ble a b) x 0 = if a ≤ b then x else 0 := by
  by_cases h : a ≤ b
  · rw [ble_true h, Bool.cond_true, ite_eq_left h]
  · rw [ble_false (not_le.1 h), Bool.cond_false, ite_eq_right h]

section Charges

variable [Grid] [IBPar]

omit [IBPar] in
/-- The lower sum of the cells `(i, j, k, l)`. -/
theorem e4_eq (i j k l : ℕ) :
    SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l = 4 * V + H * (i + j + k + l) := by
  simp only [e_eq]; ring

/-! ### The charges -/

/-- **The charges of depth 8** below the cell `(i, j, k, l, b, c, d)` of depth 7: its cells `f` of the region `reg8`,
each at its last prime's factor times `omKw`. -/
def Ch8 (i j k l b c d : ℕ) : ℕ :=
  ∑ f ∈ range (d + 1), if SieveBuch.reg8 i j k l b c d f = true then
    lastF (eC f) HC * omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f) (4 * H + 4 * HC) HC else 0

/-- **The charges of depth 7 and 8** below a decomposed cell `(i, j, k, l, b, c)` of depth 6. -/
def Ch7 (i j k l b c : ℕ) : ℕ :=
  ∑ d ∈ range (c + 1), if SieveBuch.inKK7 i j k l b c d = true then trapF (eC d) HC * Ch8 i j k l b c d else 0

/-- **The charges of depth 6 to 8** below the cell `(i, j, k, l, b)`: its counted cells of depth 6 at their bound,
or, when decomposed, at their charges below. -/
def Ch6 (i j k l b : ℕ) : ℕ :=
  ∑ c ∈ range (b + 1), if counted6 i j k l b c = true then
    (if dec6D i j k l b c = true then trapF (eC c) HC * Ch7 i j k l b c
      else q6 (i + j + k + l + 4 * b) c * SC * SC) else 0

/-- **The charges below a decomposed cell `(i, j, k, l)` of depth 4.** -/
def Ch5 (i j k l : ℕ) : ℕ :=
  ∑ b ∈ range nC, if inKK5 i j k l b = true ∧ ne5 i j k l b = true then trapF (eC b) HC * Ch6 i j k l b else 0

/-- **The charges of the row `(i, j, k)`**: its counted cells of depth 4 at their bound, or, when decomposed, at their
charges below. -/
def Ch4 (i j k : ℕ) : ℕ :=
  ∑ l ∈ range (k + 1), if counted4 i j k l = true then
    (if dec4D i j k l = true then trapF (SieveCert.e l) H * Ch5 i j k l else Q4 (i + j + k) l * SC ^ 4) else 0

/-- **The charges below the cell `(i, j)`**: its counted rows, each at the factors of `(i, j, k)` times its charges. -/
def Ch3 (i j : ℕ) : ℕ :=
  ∑ k ∈ range n, if inKK i j k = true ∧ ne3 i j k = true then P3 i j k * Ch4 i j k else 0

/-! ### Below the cells of depths 6 and 7 -/

omit [IBPar] in
/-- The charges of depth 8 are `R8in`. -/
theorem Ch8_eq (hHC : HC = 4 * H) (i j k l b c d : ℕ) :
    Ch8 i j k l b c d = R8in (i + j + k + l + 4 * b + 4 * c + 4 * d) d := by
  unfold Ch8 R8in
  rw [sumTo_eq]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [cond_ble]
  have hs : SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + eC b + eC c + eC d =
      7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d) := by
    rw [e4_eq, eC_eq, eC_eq, eC_eq, hHC]; ring
  have hr : SieveBuch.reg8 i j k l b c d f = true ↔ 7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d) + 2 * eC f ≤
      DEN := by
    unfold SieveBuch.reg8
    rw [decide_eq_true_iff, hs]
  simp only [hr]

omit [IBPar] in
/-- The charges of depths 7 and 8 are `R8`. -/
theorem Ch7_eq (hHC : HC = 4 * H) (hH : 0 < H) (i j k l b c : ℕ) :
    Ch7 i j k l b c = R8 (i + j + k + l + 4 * b + 4 * c) c := by
  unfold Ch7 R8
  rw [sumTo_eq]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [cond_ble, lit_eq, ← Ch8_eq hHC]
  have hdc : d < c + 1 := Finset.mem_range.1 hd
  have hs : SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + eC b + eC c =
      6 * V + H * (i + j + k + l + 4 * b + 4 * c) := by
    rw [e4_eq, eC_eq, eC_eq, hHC]; ring
  have hr : SieveBuch.inKK7 i j k l b c d = true ↔ 6 * V + H * (i + j + k + l + 4 * b + 4 * c) + 2 * eC d ≤ DEN := by
    unfold SieveBuch.inKK7
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, hs]
    refine and_iff_right ?_
    rw [eC_eq, eC_eq]
    have : HC * d ≤ HC * c := Nat.mul_le_mul_left _ (by omega)
    omega
  simp only [hr]

/-! ### Below a cell of depth 5 -/

omit [IBPar] in
/-- The region of the cells `c` of depth 6 below `(i, j, k, l, b)`: `c ≤ b` and `5V + H·I5 + 2eC c ≤ DEN`. -/
theorem lt_cm_of_counted6 (hHC : HC = 4 * H) (hH : 0 < H) {i j k l b c : ℕ} (hc : c < b + 1)
    (h : counted6 i j k l b c = true) :
    c < nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b)) := by
  rw [nmin_eq, lt_min_iff, lt_creg_iff (by omega)]
  refine ⟨hc, ?_⟩
  unfold counted6 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← e4_eq]
  exact h.1

/-- **A counted cell of depth 6 at its cost**: in the prefix of `cstar`, its term is at most `vR`, and beyond it, its
bound `q6`, which the masks leave. -/
theorem term6_le (hHC : HC = 4 * H) (hH : 0 < H) {i j k l b c : ℕ} (h : counted6 i j k l b c = true) :
    (c < cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC) →
      (if dec6D i j k l b c = true then trapF (eC c) HC * Ch7 i j k l b c
        else q6 (i + j + k + l + 4 * b) c * SC * SC) ≤ vR (i + j + k + l + 4 * b) c) ∧
    (cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC) ≤ c →
      (if dec6D i j k l b c = true then trapF (eC c) HC * Ch7 i j k l b c
        else q6 (i + j + k + l + 4 * b) c * SC * SC) ≤
        cond (bit (emask 1 i j k l) c || bit (emask 2 i j k l) (b + c)) 0
          (q6 (i + j + k + l + 4 * b) c * SC * SC)) := by
  have h7 := Ch7_eq hHC hH i j k l b c
  have hR : trapF (eC c) HC * lit (i + j + k + l + 4 * b + 4 * c) (fun I6 => R8 I6 c) =
      trapF (eC c) HC * Ch7 i j k l b c := by rw [lit_eq, h7]
  refine ⟨fun hcs => ?_, fun hcs => ?_⟩
  · unfold vR
    rw [hR, nmin_eq]
    unfold dec6D
    rw [blt_true hcs, Bool.true_and, ← h7]
    by_cases hlt : trapF (eC c) HC * Ch7 i j k l b c < q6 (i + j + k + l + 4 * b) c * SC * SC
    · rw [blt_true hlt, ite_eq_left rfl, min_eq_right hlt.le]
    · rw [blt_false (not_lt.1 hlt)]
      simp only [Bool.false_eq_true, ite_false]
      rw [min_eq_left (not_lt.1 hlt)]
  · have hd : dec6D i j k l b c = false := by
      unfold dec6D
      rw [blt_false hcs, Bool.false_and]
    rw [hd]
    simp only [Bool.false_eq_true, ite_false]
    have hne : surelyEval [cell i, cell j, cell k, cell l, cellC b, cellC c] = false := by
      unfold counted6 at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h.2
    have hb1 : bit (emask 1 i j k l) c = false := by
      rw [bit_eq]
      by_contra hc
      have := surelyEval6_of_emask (b := b) hHC hH (Or.inl (by simpa using hc))
      rw [hne] at this
      exact absurd this (by simp)
    have hb2 : bit (emask 2 i j k l) (b + c) = false := by
      rw [bit_eq]
      by_contra hc
      have := surelyEval6_of_emask (b := b) hHC hH (Or.inr (by simpa using hc))
      rw [hne] at this
      exact absurd this (by simp)
    rw [hb1, hb2, Bool.or_false, Bool.cond_false]

/-- The bound of a cell `c` of depth 6 beyond the prefix: `q6`, unless a mask has the box surely evaluable. -/
def tail6t (i j k l b c : ℕ) : ℕ :=
  cond (bit (emask 1 i j k l) c || bit (emask 2 i j k l) (b + c)) 0 (q6 (i + j + k + l + 4 * b) c * SC * SC)

/-- **The cells of depth 6 below `(i, j, k, l, b)`**: for a prefix `c < cs` of the region inside that of `cstar`,
whose rest of the region lies beyond it, the charges are at most the prefix at `vR` and the rest at `tail6t`. -/
theorem Ch6_le (hHC : HC = 4 * H) (hH : 0 < H) {i j k l b cs : ℕ}
    (hcm : cs ≤ nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b)))
    (hpre : ∀ c < cs, c < cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC))
    (hpost : ∀ c, cs ≤ c → c < nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b)) →
      cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC) ≤ c) :
    Ch6 i j k l b ≤ ∑ c ∈ range cs, vR (i + j + k + l + 4 * b) c +
      ∑ c ∈ Ico cs (nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b))), tail6t i j k l b c := by
  set cm := nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b)) with hcmd
  have key : Ch6 i j k l b ≤
      ∑ c ∈ range cm, (if c < cs then vR (i + j + k + l + 4 * b) c else tail6t i j k l b c) := by
    unfold Ch6
    refine sum_ite_le_sum fun c hc hcount => ?_
    have hccm : c < cm := lt_cm_of_counted6 hHC hH (Finset.mem_range.1 hc) hcount
    refine ⟨Finset.mem_range.2 hccm, ?_⟩
    have ht := term6_le hHC hH hcount
    by_cases hlt : c < cs
    · rw [ite_eq_left hlt]
      exact ht.1 (hpre c hlt)
    · rw [ite_eq_right hlt]
      exact ht.2 (hpost c (not_lt.1 hlt) hccm)
  refine key.trans (le_of_eq ?_)
  rw [← Finset.sum_range_add_sum_Ico _ hcm]
  congr 1
  · exact Finset.sum_congr rfl fun c hc => ite_eq_left (Finset.mem_range.1 hc)
  · exact Finset.sum_congr rfl fun c hc => ite_eq_right (not_lt.2 (Finset.mem_Ico.1 hc).1)

omit [IBPar] in
theorem cntH_mono {X Y : ℕ} (h : X ≤ Y) : cntH X ≤ cntH Y := by
  unfold cntH
  by_cases hX : V + HC ≤ X
  · rw [ble_true hX, ble_true (hX.trans h), Bool.cond_true, Bool.cond_true]
    exact Nat.div_le_div_right (by omega)
  · rw [ble_false (not_le.1 hX), Bool.cond_false]
    exact Nat.zero_le _

omit [IBPar] in
/-- `cstar` decreases in the upper end `hb` of the cell of `p₅`. -/
theorem cstar_anti {hi3 Dm hl hb hb' : ℕ} (h : hb ≤ hb') : cstar hi3 Dm hl hb' ≤ cstar hi3 Dm hl hb := by
  unfold cstar
  rw [nmax_eq, nmax_eq, nmin_eq, nmin_eq]
  have hA : cond (Nat.blt (hi3 + hl + hb') lim) (cntH ((lim - hi3 - hl - hb' - 1) / 2)) 0 ≤
      cond (Nat.blt (hi3 + hl + hb) lim) (cntH ((lim - hi3 - hl - hb - 1) / 2)) 0 := by
    by_cases h' : hi3 + hl + hb' < lim
    · rw [blt_true h', blt_true (by omega : hi3 + hl + hb < lim), Bool.cond_true, Bool.cond_true]
      exact cntH_mono (Nat.div_le_div_right (by omega))
    · rw [blt_false (not_lt.1 h'), Bool.cond_false]
      exact Nat.zero_le _
  have hB : cond (Nat.blt (hi3 + hl + hb') DEN) (cntH ((DEN - hi3 - hl - hb' - 1) / 3)) 0 ≤
      cond (Nat.blt (hi3 + hl + hb) DEN) (cntH ((DEN - hi3 - hl - hb - 1) / 3)) 0 := by
    by_cases h' : hi3 + hl + hb' < DEN
    · rw [blt_true h', blt_true (by omega : hi3 + hl + hb < DEN), Bool.cond_true, Bool.cond_true]
      exact cntH_mono (Nat.div_le_div_right (by omega))
    · rw [blt_false (not_lt.1 h'), Bool.cond_false]
      exact Nat.zero_le _
  have hC : cond (Nat.blt (hl + hb') Dm) (cntH ((Dm - hl - hb' - 1) / 2)) 0 ≤
      cond (Nat.blt (hl + hb) Dm) (cntH ((Dm - hl - hb - 1) / 2)) 0 := by
    by_cases h' : hl + hb' < Dm
    · rw [blt_true h', blt_true (by omega : hl + hb < Dm), Bool.cond_true, Bool.cond_true]
      exact cntH_mono (Nat.div_le_div_right (by omega))
    · rw [blt_false (not_lt.1 h'), Bool.cond_false]
      exact Nat.zero_le _
  exact max_le_max hA (min_le_min hB hC)

omit [IBPar] in
/-- `creg` decreases in the lower sum. -/
theorem creg_anti {S S' : ℕ} (hHC : 0 < HC) (h : S ≤ S') : creg S' ≤ creg S := by
  by_contra hc
  have h1 := (lt_creg_iff (S := S') hHC).1 (not_le.1 hc)
  have h2 := (lt_creg_iff (S := S) (c := creg S) hHC).2 (by omega)
  exact absurd h2 (lt_irrefl _)

omit [IBPar] in
/-- The prefix and the rest of the region of `p₆` below `(…, b)`, with `vRpre` and `tail6`. -/
theorem prefix_eq (I5 cs : ℕ) : cond (Nat.beq cs 0) 0 (lit (cs - 1) (fun c => vRpre I5 c)) =
    ∑ c ∈ range cs, vR I5 c := by
  rcases Nat.eq_zero_or_pos cs with h | h
  · subst h; rfl
  · rw [show Nat.beq cs 0 = false from beq_false (by omega), Bool.cond_false, lit_eq]
    unfold vRpre
    rw [sumTo_eq, Nat.sub_add_cancel h]

omit [IBPar] in
theorem tail_eq {i j k l b cs cm : ℕ} :
    cond (Nat.blt cs cm) (tail6 (i + j + k + l + 4 * b) b cs cm (emask 1 i j k l) (emask 2 i j k l)) 0 =
      ∑ c ∈ Ico cs cm, tail6t i j k l b c := by
  by_cases h : cs < cm
  · rw [blt_true h, Bool.cond_true, tail6, sumTo_eq, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [lit_eq, tail6t, Nat.add_assoc]
  · rw [blt_false (not_lt.1 h), Bool.cond_false, Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- **Below a decomposed cell of depth 4, not every box passing**: the charges are at most `cost6`. -/
theorem Ch5_le_cost6 (hHC : HC = 4 * H) (hH : 0 < H) {i j k l : ℕ} :
    Ch5 i j k l ≤ cost6 (hi3 i j k) (dmax3 i j k) (i + j + k + l) l (emask 1 i j k l) (emask 2 i j k l) := by
  unfold Ch5 cost6
  rw [sumTo_eq]
  refine sum_ite_le_sum fun b hb hK => ?_
  refine ⟨Finset.mem_range.2 ((inKK5_iff hHC hH).1 hK.1), ?_⟩
  have hnb : bit (emask 1 i j k l) b = false := by
    rw [bit_eq]
    by_contra hc
    have := surelyEval5_of_emask hHC hH (by simpa using hc)
    have h2 := hK.2
    simp only [ne5, this, Bool.not_true] at h2
    exact absurd h2 (by simp)
  rw [hnb, Bool.cond_false]
  unfold cost6b
  simp only []
  rw [lit_eq]
  refine Nat.mul_le_mul_left _ ?_
  set cm := nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b)) with hcm
  set cs := nmin cm (cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC)) with hcsd
  have e5 : i + j + k + l + 4 * b = i + j + k + l + 4 * b := rfl
  rw [prefix_eq, tail_eq]
  refine Ch6_le hHC hH (by rw [hcsd, nmin_eq]; exact min_le_left _ _) (fun c hc => ?_) (fun c hc hc' => ?_)
  · rw [hcsd, nmin_eq] at hc
    exact lt_of_lt_of_le hc (min_le_right _ _)
  · rw [hcsd, nmin_eq] at hc
    rcases min_choice cm (cstar (hi3 i j k) (dmax3 i j k) (SieveCert.e l + H) (eC b + HC)) with hm | hm
    · rw [hm] at hc; omega
    · rw [hm] at hc; exact hc

/-- **Below a decomposed cell of depth 4 whose boxes below all pass**: the charges are at most `Fpure`. -/
theorem Ch5_le_Fpure (hHC : HC = 4 * H) (hH : 0 < H) {i j k l : ℕ}
    (hp : pureOK (hi3 i j k) (dmax3 i j k) (i + j + k + l) l = true) :
    Ch5 i j k l ≤ Fpure (i + j + k + l) l := by
  have hHC0 : 0 < HC := by omega
  unfold pureOK at hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hbc, -⟩, hcs⟩ := hp
  have hbc' : bcnt (i + j + k + l) l ≠ 0 := Nat.ne_of_beq_eq_false hbc
  have hcs' := Nat.le_of_ble_eq_true hcs
  unfold Ch5 Fpure
  rw [sumTo_eq]
  refine sum_ite_le_sum fun b hb hK => ?_
  have hbl : b < bcnt (i + j + k + l) l := (inKK5_iff hHC hH).1 hK.1
  refine ⟨Finset.mem_range.2 hbl, ?_⟩
  simp only []
  set cm := nmin (b + 1) (creg (4 * V + H * (i + j + k + l) + eC b)) with hcm
  have h6 := Ch6_le (cs := cm) hHC hH le_rfl (fun c hc => ?_) (fun c hc hc' => absurd hc' (by omega))
  · rw [Finset.Ico_self, Finset.sum_empty, add_zero] at h6
    rcases Nat.eq_zero_or_pos cm with h0 | h0
    · rw [h0, Finset.sum_range_zero] at h6
      rw [nonpos_iff_eq_zero.1 h6, Nat.mul_zero]
      exact Nat.zero_le _
    · rw [show Nat.beq cm 0 = false from beq_false (by omega), Bool.cond_false, lit_eq, lit_eq]
      refine Nat.mul_le_mul_left _ (h6.trans (le_of_eq ?_))
      unfold vRpre
      rw [sumTo_eq, Nat.sub_add_cancel h0]
  · -- the prefix: `c < cm` lies in `cstar` at the region's last `b`, hence at `b`
    rw [hcm, nmin_eq, lt_min_iff] at hc
    have h1 : c < nmin (bcnt (i + j + k + l) l) (creg (4 * V + H * (i + j + k + l) + V)) := by
      rw [nmin_eq, lt_min_iff]
      refine ⟨by omega, lt_of_lt_of_le hc.2 (creg_anti hHC0 ?_)⟩
      rw [eC_eq]; omega
    refine lt_of_lt_of_le (lt_of_lt_of_le h1 hcs') (cstar_anti ?_)
    rw [eC_eq, eC_eq]
    have : HC * b ≤ HC * (bcnt (i + j + k + l) l - 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- **A counted cell of depth 4 at its cost**: its term is at most `cost4`. -/
theorem term4_le (hHC : HC = 4 * H) (hH : 0 < H) {i j k l : ℕ} :
    (if dec4D i j k l = true then trapF (SieveCert.e l) H * Ch5 i j k l else Q4 (i + j + k) l * SC ^ 4) ≤
      cost4 i j k l := by
  have h5p := fun hp => Ch5_le_Fpure (i := i) (j := j) (k := k) (l := l) hHC hH hp
  have h5c := Ch5_le_cost6 (i := i) (j := j) (k := k) (l := l) hHC hH
  unfold cost4 dec4D hi3 at *
  simp only [lit_eq]
  by_cases hok : okD (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k) (SieveCert.e l + H)
      (SieveCert.e l + H) = true
  · rw [hok, Bool.true_and, Bool.cond_true]
    by_cases hp : pureOK (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k) (i + j + k + l) l =
        true
    · rw [hp, Bool.cond_true, Bool.cond_true]
      unfold Gpure
      simp only [lit_eq]
      rw [nmin_eq]
      by_cases hlt : trapF (SieveCert.e l) H * Fpure (i + j + k + l) l < Q4 (i + j + k) l * SC ^ 4
      · rw [blt_true hlt, ite_eq_left rfl, min_eq_right hlt.le]
        exact Nat.mul_le_mul_left _ (h5p hp)
      · rw [blt_false (not_lt.1 hlt), min_eq_left (not_lt.1 hlt)]
        simp
    · have hpf : pureOK (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k) (i + j + k + l) l =
          false := by simpa using hp
      rw [hpf, Bool.cond_false, Bool.cond_false]
      by_cases hb : bad5 (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k) (i + j + k + l) l
          (emask 1 i j k l) = 0
      · rw [hb, show Nat.beq 0 0 = true from rfl, Bool.true_and, Bool.cond_true, nmin_eq]
        by_cases hlt : trapF (SieveCert.e l) H * cost6 (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H)
            (dmax3 i j k) (i + j + k + l) l (emask 1 i j k l) (emask 2 i j k l) < Q4 (i + j + k) l * SC ^ 4
        · rw [blt_true hlt, ite_eq_left rfl, min_eq_right hlt.le]
          exact Nat.mul_le_mul_left _ h5c
        · rw [blt_false (not_lt.1 hlt), min_eq_left (not_lt.1 hlt)]
          simp
      · rw [beq_false hb, Bool.false_and, Bool.cond_false]
        simp
  · have hokf : okD (SieveCert.e i + SieveCert.e j + SieveCert.e k + 3 * H) (dmax3 i j k) (SieveCert.e l + H)
        (SieveCert.e l + H) = false := by simpa using hok
    rw [hokf, Bool.false_and, Bool.cond_false]
    simp

/-- **The row `(i, j, k)`**: its charges are at most `row`. -/
theorem Ch4_le_row (hHC : HC = 4 * H) (hH : 0 < H) {i j k : ℕ} : Ch4 i j k ≤ row i j k := by
  unfold Ch4 row
  simp only []
  rw [sumTo_eq]
  refine sum_ite_le_sum fun l hl hc => ?_
  have hc' := hc
  unfold counted4 at hc'
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc'
  refine ⟨Finset.mem_range.2 ?_, ?_⟩
  · rw [nmin_eq, lt_min_iff, lt_lreg_iff hH]
    exact ⟨Finset.mem_range.1 hl, hc'.1⟩
  · have hnb : bit (lmask i j k) l = false := by
      rw [bit_eq]
      by_contra hb
      have := surelyEval4_of_lmask hH (by simpa using hb)
      rw [hc'.2] at this
      exact absurd this (by simp)
    rw [hnb, Bool.cond_false]
    exact term4_le hHC hH

/-- **The charges below a cell `(i, j)` are at most `SC⁸·refcost`.** -/
theorem Ch3_le (hHC : HC = 4 * H) (hH : 0 < H) {i j : ℕ} : Ch3 i j ≤ SC ^ 8 * refcost i j := by
  unfold Ch3 refcost
  have hS : 0 < SC ^ 8 := by unfold SC; positivity
  set X := sumTo n (fun k => cond (inKK i j k && ne3 i j k) (P3 i j k * row i j k) 0) with hX
  have h1 : ∑ k ∈ range n, (if inKK i j k = true ∧ ne3 i j k = true then P3 i j k * Ch4 i j k else 0) ≤ X := by
    rw [hX, sumTo_eq]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : inKK i j k = true ∧ ne3 i j k = true
    · rw [ite_eq_left hk, hk.1, hk.2, Bool.and_true, Bool.cond_true]
      exact Nat.mul_le_mul_left _ (Ch4_le_row hHC hH)
    · rw [ite_eq_right hk]
      exact Nat.zero_le _
  refine h1.trans ?_
  unfold cdiv
  have h2 := Nat.div_add_mod (X + SC ^ 8 - 1) (SC ^ 8)
  have h3 := Nat.mod_lt (X + SC ^ 8 - 1) hS
  omega

end Charges

end SieveDeep
