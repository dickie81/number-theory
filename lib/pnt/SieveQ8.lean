/-
# The leaves of the decomposition to depth 8, for large `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. As `SieveQ.lean`, for the decomposition to depth 8 of `SieveBuch8.lean` (`SieveBuch.Par.Leaves8`),
under a scheme of decisions (`SieveBuch.Scheme8`).

* `thrOK_S6cle` … `thrOK_S7gt`, `nz_S6cle`, `nz_S7le`, `len_S6cle` … `len_S7gt`: the families at depths 6 and 7 have
  at most `40` atoms with thresholds in `[1, q^{L+1}]`, and the parts at or below the thresholds nonzero
  coefficients.
* `lf_e6gt`, `lf_p6`, `lf_e7gt`, `lf_p7`: the leaves at depths 6 and 7, for boxes that the rule passes: the part
  above the threshold by the upper window (split) or empty (whole), the part at or below it by Proposition 6 (split)
  or Proposition 6-ib (whole).
* `boxes6`, `boxes7`: the grid's boxes of depths 6 and 7, four fine cells and two or three coarse ones.
* `leaves_ev8`: for a rule with `RuleIB`, its exponent the route's (`IBFits`), a scheme, and the route's Type II
  estimate (`hII`): for `η > 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and `a` a unit mod `q`, `LargeQ q`
  holds and every leaf of `(parQ q).Leaves8` is within `Err η δ q`.

The proof of `leaves_ev8` is that of `SieveQ.leaves_ev`, with the upper window for six and seven primes, Proposition 6
for six and seven, and Proposition 6-ib on `boxes6` and `boxes7` besides; a decision of the scheme gives the rule's
verdict on the boxes it decomposes (`SieveBuch.ok2_of_dec2` … `SieveBuch.ok7_of_allowed6R`).

The file imports `SieveBuch8.lean` and `SieveQ.lean`.
-/
import SieveBuch8
import SieveQ

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveRoute SieveQ
open SieveCert (V DEN H U1 U2 cand inKK ne3 counted4 surelyEval cell inside lim limOK nbOK nC eC HC cellC inKK5
  ne5 counted6)

namespace SieveQ8

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-! ### The families at depths 6 and 7 -/

section Families

variable {q : ℕ} (hL : LargeQ q)
include hL

theorem thrOK_S6cle [SieveCert.GridOKC] {i j k l b c : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < nC) (hc : c < nC) :
    ThrOK q ((parQ q).S6cle i j k l b c) :=
  thrOK_append (thrOK_S6c hL hi hj hk hl hb hc) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S6cgt [SieveCert.GridOKC] {i j k l b c : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < nC) (hc : c < nC) :
    ThrOK q ((parQ q).S6cgt i j k l b c) :=
  thrOK_append (thrOK_S6c hL hi hj hk hl hb hc) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S7 [SieveCert.GridOKC] {i j k l b c : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < nC) (hc : c < nC) :
    ThrOK q ((parQ q).S7 i j k l b c) :=
  thrOK_extS (thrOK_S6cle hL hi hj hk hl hb hc) (thr_bounds hL).1.1 (thr_bounds hL).1.2 (q1 hL)

theorem thrOK_S7c [SieveCert.GridOKC] {i j k l b c d : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < nC) (hc : c < nC) (hd : d < nC) :
    ThrOK q ((parQ q).S7c i j k l b c d) :=
  thrOK_append (thrOK_S7 hL hi hj hk hl hb hc) (thrOK_cellAC (q1 hL) 6 hd)

theorem thrOK_S7le [SieveCert.GridOKC] {i j k l b c d : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < nC) (hc : c < nC) (hd : d < nC) :
    ThrOK q ((parQ q).S7le i j k l b c d) :=
  thrOK_append (thrOK_S7c hL hi hj hk hl hb hc hd) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

theorem thrOK_S7gt [SieveCert.GridOKC] {i j k l b c d : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) (hl : l < SieveCert.n) (hb : b < nC) (hc : c < nC) (hd : d < nC) :
    ThrOK q ((parQ q).S7gt i j k l b c d) :=
  thrOK_append (thrOK_S7c hL hi hj hk hl hb hc hd) (thrOK_single (thr_Xs hL _).1 (thr_Xs hL _).2)

end Families

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S6cle (q i j k l b c : ℕ) : ∀ A ∈ (parQ q).S6cle i j k l b c, NZ A := by
  refine nz_append (nz_append (nz_extS (nz_S5le q i j k l b)) ?_) (nz_prodLe _)
  exact @nz_cellA (SieveCert.Gc) 6 5 ((q : ℝ) ^ L) c

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem nz_S7le (q i j k l b c d : ℕ) : ∀ A ∈ (parQ q).S7le i j k l b c d, NZ A := by
  refine nz_append (nz_append (nz_extS (nz_S6cle q i j k l b c)) ?_) (nz_prodLe _)
  exact @nz_cellA (SieveCert.Gc) 7 6 ((q : ℝ) ^ L) d

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S6cle (q i j k l b c : ℕ) : ((parQ q).S6cle i j k l b c).length ≤ 40 := by
  simp [Par.S6cle, Par.S6c, Par.S6, Par.S5le, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3,
    Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellAC, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S6cgt (q i j k l b c : ℕ) : ((parQ q).S6cgt i j k l b c).length ≤ 40 := by
  simp [Par.S6cgt, Par.S6c, Par.S6, Par.S5le, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4, Par.S3le, Par.S3c, Par.S3,
    Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellAC, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S7le (q i j k l b c d : ℕ) : ((parQ q).S7le i j k l b c d).length ≤ 40 := by
  simp [Par.S7le, Par.S7c, Par.S7, Par.S6cle, Par.S6c, Par.S6, Par.S5le, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4,
    Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellAC, cellA, extS]
omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_S7gt (q i j k l b c d : ℕ) : ((parQ q).S7gt i j k l b c d).length ≤ 40 := by
  simp [Par.S7gt, Par.S7c, Par.S7, Par.S6cle, Par.S6c, Par.S6, Par.S5le, Par.S5c, Par.S5, Par.S4cle, Par.S4c, Par.S4,
    Par.S3le, Par.S3c, Par.S3, Par.S2le, Par.S2c, Par.S2, Par.S1c, Par.S1, cellAC, cellA, extS]

/-! ### The leaves at depths 6 and 7 -/

section Leaves

variable {q : ℕ} (hL : LargeQ q) {a : ZMod q} {E : ℝ}
include hL

theorem lf_e6gt [SieveCert.GridOKC] [SieveCert.Rule] [SieveCert.RuleNB] (hE : 0 ≤ E) (hT : TUat q a 5 E)
    {i j k l b c : ℕ} (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < nC)
    (hc : c < nC) (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c] = true) :
    |(parQ q).I (gA q a) ((parQ q).S6cgt i j k l b c) - (parQ q).I (gB q) ((parQ q).S6cgt i j k l b c)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hfacts : ∀ {Y : ℕ} (rt : Fin 6 → ℕ), rt ∈ famSet 6 Y ((parQ q).S6cgt i j k l b c) →
      (∀ t, (rt t : ℝ) < xq q ^ ((((![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H,
        SieveCert.e l + H, eC b + HC, eC c + HC] : Fin 6 → ℕ) t : ℕ) : ℝ) / DEN)) ∧
        (parQ q).Xs (sp6 i j k l b c) < ∏ t ∈ Finset.univ, (rt t : ℝ) := by
    intro Y rt hrt
    obtain ⟨-, hCi, hCj, hCk, hCl, hCb, hCc, -⟩ :=
      (parQ q).facts_S6c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb := inCC_iff.1 (show InCC (xq q) b (rt 4) from hCb)
    have hCc := inCC_iff.1 (show InCC (xq q) c (rt 5) from hCc)
    refine ⟨fun t => ?_, sem_of_mem hrt (A := Atom.prodGt Finset.univ ((parQ q).Xs (sp6 i j k l b c)))
      (List.mem_append_right _ (List.mem_singleton_self _))⟩
    fin_cases t
    · simpa using hCi.2
    · simpa using hCj.2
    · simpa using hCk.2
    · simpa using hCl.2
    · simpa using hCb.2
    · simpa using hCc.2
  by_cases hs : sp6 i j k l b c = true
  · have hT6 : SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) +
        (eC b + HC) + (eC c + HC) < lim := by
      simpa [sp6, limOK_cells6] using hs
    refine hT _ (parQ q).Xp (W1 q) (len_S6cgt q i j k l b c) (thrOK_S6cgt hL hi hj hk hl hb hc)
      (fun rt hp hs' => ?_) (W1_le hL) (W1_div hL) (W0_div hL)
    have hrt := mem_famSet_sum hp hs'
    obtain ⟨hch, -⟩ := (parQ q).facts_S6c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    obtain ⟨hb6, hgt⟩ := hfacts rt hrt
    rw [hs, Par.Xs_true] at hgt
    refine ⟨hch.1, ha0_of hch.2.1, by exact_mod_cast hgt, ?_⟩
    have := window_hi_gen hq1 hb6 (T := Finset.univ) (B := DEN - U1) (by
      simp [Fin.sum_univ_six, SieveCert.lim] at hT6 ⊢
      omega)
    simpa using this
  · have hs' : sp6 i j k l b c = false := by simpa using hs
    have hnb : nbOK [cell i, cell j, cell k, cell l, cellC b, cellC c] = true :=
      (SieveCert.RuleNB.nb _ hok).resolve_left hs
    rw [nbOK_cells6, decide_eq_true_eq] at hnb
    have hz : ∀ g, (parQ q).I g ((parQ q).S6cgt i j k l b c) = 0 := fun g =>
      famI_whole_gt hL g ![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H, SieveCert.e l + H, eC b + HC,
        eC c + HC] (by simp [Fin.sum_univ_six]; omega) fun rt hrt => by
          obtain ⟨hb6, hgt⟩ := hfacts rt hrt
          rw [hs', Par.Xs_false] at hgt
          exact ⟨hgt, hb6⟩
    rw [hz, hz, sub_zero, abs_zero]
    exact hE

theorem lf_p6 [SieveCert.GridOKC] [SieveCert.Rule] [SieveCert.IBPar] [SieveCert.RuleIB] (hP : P6at q a 6 E)
    {i j k l b c : ℕ} (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < nC)
    (hc : c < nC) (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c] = true)
    (hIB : SieveCert.ibOK [cell i, cell j, cell k, cell l, cellC b, cellC c] = true →
      P6IBat q a ![cell i, cell j, cell k, cell l, cellC b, cellC c] E) :
    |(parQ q).J (gA q a) ((parQ q).S6cle i j k l b c) - (parQ q).J (gB q) ((parQ q).S6cle i j k l b c)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  by_cases hs : sp6 i j k l b c = true
  · refine hP _ (len_S6cle q i j k l b c) (thrOK_S6cle hL hi hj hk hl hb hc) (nz_S6cle q i j k l b c)
      fun rt hp hs' => ?_
    obtain ⟨hch, -, -, -, -, -, -, -, -, -, -, hX⟩ := (parQ q).facts_S6cle (mem_famSet_sum hp hs')
    rw [hs, Par.Xs_true] at hX
    refine ⟨hch.2.1, ?_⟩
    rw [Fin.prod_univ_six]
    exact_mod_cast hX
  · have hib := ((SieveCert.RuleIB.ib _ hok).resolve_left hs).1
    refine hIB hib _ (len_S6cle q i j k l b c) (thrOK_S6cle hL hi hj hk hl hb hc) fun rt hp hs' => ?_
    obtain ⟨hch, hCi, hCj, hCk, hCl, hCb, hCc, -⟩ := (parQ q).facts_S6cle (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb := inCC_iff.1 (show InCC (xq q) b (rt 4) from hCb)
    have hCc := inCC_iff.1 (show InCC (xq q) c (rt 5) from hCc)
    refine ⟨hch.1, hch.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩
    · exact ⟨by simpa [cell] using hCl.1, by simpa [cell] using hCl.2⟩
    · exact ⟨by simpa [cellC] using hCb.1, by simpa [cellC] using hCb.2⟩
    · exact ⟨by simpa [cellC] using hCc.1, by simpa [cellC] using hCc.2⟩

theorem lf_e7gt [SieveCert.GridOKC] [SieveCert.Rule] [SieveCert.RuleNB] (hE : 0 ≤ E) (hT : TUat q a 6 E)
    {i j k l b c d : ℕ} (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < nC)
    (hc : c < nC) (hd : d < nC)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true) :
    |(parQ q).I (gA q a) ((parQ q).S7gt i j k l b c d) - (parQ q).I (gB q) ((parQ q).S7gt i j k l b c d)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hfacts : ∀ {Y : ℕ} (rt : Fin 7 → ℕ), rt ∈ famSet 7 Y ((parQ q).S7gt i j k l b c d) →
      (∀ t, (rt t : ℝ) < xq q ^ ((((![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H,
        SieveCert.e l + H, eC b + HC, eC c + HC, eC d + HC] : Fin 7 → ℕ) t : ℕ) : ℝ) / DEN)) ∧
        (parQ q).Xs (sp7 i j k l b c d) < ∏ t ∈ Finset.univ, (rt t : ℝ) := by
    intro Y rt hrt
    obtain ⟨-, hCi, hCj, hCk, hCl, hCb, hCc, hCd, -⟩ :=
      (parQ q).facts_S7c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb := inCC_iff.1 (show InCC (xq q) b (rt 4) from hCb)
    have hCc := inCC_iff.1 (show InCC (xq q) c (rt 5) from hCc)
    have hCd := inCC_iff.1 (show InCC (xq q) d (rt 6) from hCd)
    refine ⟨fun t => ?_, sem_of_mem hrt (A := Atom.prodGt Finset.univ ((parQ q).Xs (sp7 i j k l b c d)))
      (List.mem_append_right _ (List.mem_singleton_self _))⟩
    fin_cases t
    · simpa using hCi.2
    · simpa using hCj.2
    · simpa using hCk.2
    · simpa using hCl.2
    · simpa using hCb.2
    · simpa using hCc.2
    · simpa using hCd.2
  by_cases hs : sp7 i j k l b c d = true
  · have hT7 : SieveCert.e i + H + (SieveCert.e j + H) + (SieveCert.e k + H) + (SieveCert.e l + H) +
        (eC b + HC) + (eC c + HC) + (eC d + HC) < lim := by
      simpa [sp7, limOK_cells7] using hs
    refine hT _ (parQ q).Xp (W1 q) (len_S7gt q i j k l b c d) (thrOK_S7gt hL hi hj hk hl hb hc hd)
      (fun rt hp hs' => ?_) (W1_le hL) (W1_div hL) (W0_div hL)
    have hrt := mem_famSet_sum hp hs'
    obtain ⟨hch, -⟩ := (parQ q).facts_S7c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
    obtain ⟨hb7, hgt⟩ := hfacts rt hrt
    rw [hs, Par.Xs_true] at hgt
    refine ⟨hch.1, ha0_of hch.2.1, by exact_mod_cast hgt, ?_⟩
    have := window_hi_gen hq1 hb7 (T := Finset.univ) (B := DEN - U1) (by
      simp [Fin.sum_univ_seven, SieveCert.lim] at hT7 ⊢
      omega)
    simpa using this
  · have hs' : sp7 i j k l b c d = false := by simpa using hs
    have hnb : nbOK [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true :=
      (SieveCert.RuleNB.nb _ hok).resolve_left hs
    rw [nbOK_cells7, decide_eq_true_eq] at hnb
    have hz : ∀ g, (parQ q).I g ((parQ q).S7gt i j k l b c d) = 0 := fun g =>
      famI_whole_gt hL g ![SieveCert.e i + H, SieveCert.e j + H, SieveCert.e k + H, SieveCert.e l + H, eC b + HC,
        eC c + HC, eC d + HC] (by simp [Fin.sum_univ_seven]; omega) fun rt hrt => by
          obtain ⟨hb7, hgt⟩ := hfacts rt hrt
          rw [hs', Par.Xs_false] at hgt
          exact ⟨hgt, hb7⟩
    rw [hz, hz, sub_zero, abs_zero]
    exact hE

theorem lf_p7 [SieveCert.GridOKC] [SieveCert.Rule] [SieveCert.IBPar] [SieveCert.RuleIB] (hP : P6at q a 7 E)
    {i j k l b c d : ℕ} (hx : i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n) (hb : b < nC)
    (hc : c < nC) (hd : d < nC)
    (hok : SieveCert.Rule.ok [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true)
    (hIB : SieveCert.ibOK [cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] = true →
      P6IBat q a ![cell i, cell j, cell k, cell l, cellC b, cellC c, cellC d] E) :
    |(parQ q).J (gA q a) ((parQ q).S7le i j k l b c d) - (parQ q).J (gB q) ((parQ q).S7le i j k l b c d)| ≤ E := by
  obtain ⟨hi, hj, hk, hl⟩ := hx
  by_cases hs : sp7 i j k l b c d = true
  · refine hP _ (len_S7le q i j k l b c d) (thrOK_S7le hL hi hj hk hl hb hc hd) (nz_S7le q i j k l b c d)
      fun rt hp hs' => ?_
    obtain ⟨hch, -, -, -, -, -, -, -, -, -, -, -, -, hX⟩ := (parQ q).facts_S7le (mem_famSet_sum hp hs')
    rw [hs, Par.Xs_true] at hX
    refine ⟨hch.2.1, ?_⟩
    rw [Fin.prod_univ_seven]
    exact_mod_cast hX
  · have hib := ((SieveCert.RuleIB.ib _ hok).resolve_left hs).1
    refine hIB hib _ (len_S7le q i j k l b c d) (thrOK_S7le hL hi hj hk hl hb hc hd) fun rt hp hs' => ?_
    obtain ⟨hch, hCi, hCj, hCk, hCl, hCb, hCc, hCd, -⟩ := (parQ q).facts_S7le (mem_famSet_sum hp hs')
    have hCi : InC (xq q) i (rt 0) := hCi
    have hCj : InC (xq q) j (rt 1) := hCj
    have hCk : InC (xq q) k (rt 2) := hCk
    have hCl : InC (xq q) l (rt 3) := hCl
    have hCb := inCC_iff.1 (show InCC (xq q) b (rt 4) from hCb)
    have hCc := inCC_iff.1 (show InCC (xq q) c (rt 5) from hCc)
    have hCd := inCC_iff.1 (show InCC (xq q) d (rt 6) from hCd)
    refine ⟨hch.1, hch.2.1, fun t => ?_⟩
    fin_cases t
    · exact ⟨by simpa [cell] using hCi.1, by simpa [cell] using hCi.2⟩
    · exact ⟨by simpa [cell] using hCj.1, by simpa [cell] using hCj.2⟩
    · exact ⟨by simpa [cell] using hCk.1, by simpa [cell] using hCk.2⟩
    · exact ⟨by simpa [cell] using hCl.1, by simpa [cell] using hCl.2⟩
    · exact ⟨by simpa [cellC] using hCb.1, by simpa [cellC] using hCb.2⟩
    · exact ⟨by simpa [cellC] using hCc.1, by simpa [cellC] using hCc.2⟩
    · exact ⟨by simpa [cellC] using hCd.1, by simpa [cellC] using hCd.2⟩

end Leaves

/-- The boxes of depth 6 of the grid: four fine cells and two coarse ones. -/
def boxes6 : Finset (Fin 6 → ℕ × ℕ) :=
  (Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ
    Finset.range nC ×ˢ Finset.range nC).image
      fun p => ![cell p.1, cell p.2.1, cell p.2.2.1, cell p.2.2.2.1, cellC p.2.2.2.2.1, cellC p.2.2.2.2.2]

/-- The boxes of depth 7 of the grid: four fine cells and three coarse ones. -/
def boxes7 : Finset (Fin 7 → ℕ × ℕ) :=
  (Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ Finset.range SieveCert.n ×ˢ
    Finset.range nC ×ˢ Finset.range nC ×ˢ Finset.range nC).image
      fun p => ![cell p.1, cell p.2.1, cell p.2.2.1, cell p.2.2.2.1, cellC p.2.2.2.2.1, cellC p.2.2.2.2.2.1,
        cellC p.2.2.2.2.2.2]

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The prefix of depth 4 of the decomposition to depth 8: all four indices are below `n`. -/
theorem deep'_idx [SieveCert.Rule] [Scheme8] {i j k l : ℕ} (h : Deep' i j k l) :
    i < SieveCert.n ∧ j < SieveCert.n ∧ k < SieveCert.n ∧ l < SieveCert.n :=
  ⟨h.1.1.1, h.1.1.2.1, h.1.2.1, by have := h.1.2.1; have := h.2.1; omega⟩

/-- **The leaves of the decomposition to depth 8, for large `q`.** For a route with `RouteOK` and a grid with
`GridOK` and `GridOKC` that fit (`Fits`), a rule that splits and decomposes a box only when `limOK` passes it, or the
bilinear Type I test with no boundary term does (`RuleIB`), its exponent the route's (`IBFits`), a scheme, and the
route's Type II estimate (`hII`): for `η > 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and `a` a unit mod
`q`, `q` is large and every leaf of the tree at `x = q^L` is within `Err η δ q`. -/
theorem leaves_ev8 [SieveCert.GridOKC] [SieveCert.Rule] [SieveCert.IBPar] [SieveCert.RuleIB] [IBFits] [Scheme8]
    (hII : TypeIIAt) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      LargeQ q ∧ (parQ q).Leaves8 (gA q a) (gB q) (Err η δ q) := by
  have : SieveCert.RuleNB := SieveCert.RuleIB.toRuleNB
  obtain ⟨d1, hd1, q1, h1⟩ := TL_spec a0 hII a0_pos 0
  obtain ⟨d2, hd2, q2, h2⟩ := TL_spec a0 hII a0_pos 1
  obtain ⟨d3, hd3, q3, h3⟩ := TL_spec a0 hII a0_pos 2
  obtain ⟨d4, hd4, q4, h4⟩ := TL_spec a0 hII a0_pos 3
  obtain ⟨d5, hd5, q5, h5⟩ := TL_spec a0 hII a0_pos 4
  obtain ⟨d6, hd6, q6, h6⟩ := TL_spec a0 hII a0_pos 5
  obtain ⟨d7, hd7, q7, h7⟩ := TU_spec a0 hII a0_pos 1
  obtain ⟨d8, hd8, q8, h8⟩ := TU_spec a0 hII a0_pos 2
  obtain ⟨d9, hd9, q9, h9⟩ := TU_spec a0 hII a0_pos 3
  obtain ⟨d10, hd10, q10, h10⟩ := TU_spec a0 hII a0_pos 4
  obtain ⟨d11, hd11, q11, h11⟩ := TU_spec a0 hII a0_pos 5
  obtain ⟨d12, hd12, q12, h12⟩ := TU_spec a0 hII a0_pos 6
  obtain ⟨d13, hd13, q13, h13⟩ := TR_spec a0 hII a0_pos 1
  obtain ⟨d14, hd14, q14, h14⟩ := TR_spec a0 hII a0_pos 2
  obtain ⟨d15, hd15, q15, h15⟩ := TR_spec a0 hII a0_pos 3
  obtain ⟨d16, hd16, q16, h16⟩ := TR_spec a0 hII a0_pos 4
  obtain ⟨d17, hd17, q17, h17⟩ := TR_spec a0 hII a0_pos 5
  obtain ⟨d18, hd18, q18, h18⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 0 hη
  obtain ⟨d19, hd19, q19, h19⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 1 hη
  obtain ⟨d20, hd20, q20, h20⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 2 hη
  obtain ⟨d21, hd21, q21, h21⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 3 hη
  obtain ⟨d22, hd22, q22, h22⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 4 hη
  obtain ⟨d23, hd23, q23, h23⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 5 hη
  obtain ⟨d24, hd24, q24, h24⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 6 hη
  obtain ⟨d25, hd25, q25, h25⟩ := P6_spec a0 b0 hII a0_pos a0_b0 b0_gt b0_lt 7 hη
  obtain ⟨d26, hd26, q26, h26⟩ := P6IB_boxes hII boxes2 hη
  obtain ⟨d27, hd27, q27, h27⟩ := P6IB_boxes hII boxes3 hη
  obtain ⟨d28, hd28, q28, h28⟩ := P6IB_boxes hII boxes4 hη
  obtain ⟨d29, hd29, q29, h29⟩ := P6IB_boxes hII boxes5 hη
  obtain ⟨d30, hd30, q30, h30⟩ := P6IB_boxes hII boxes6 hη
  obtain ⟨d31, hd31, q31, h31⟩ := P6IB_boxes hII boxes7 hη
  obtain ⟨qL, hqL⟩ := Filter.eventually_atTop.1 (largeQ_ev)
  obtain ⟨δ, hδ0, hle⟩ := exists_le_list [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17,
    d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31]
    (by simp [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
      hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29, hd30, hd31])
  refine ⟨δ, hδ0, q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 + q16 + q17 + q18 +
    q19 + q20 + q21 + q22 + q23 + q24 + q25 + q26 + q27 + q28 + q29 + q30 + q31 + qL, fun q _ hq a ha => ?_⟩
  have hLq : LargeQ q := hqL q (by omega)
  have hq1 : 1 ≤ q := by have := hLq.q3; omega
  have hE0 := Err_nonneg hη δ q hq1
  have tl0 : TLat q a 0 (Err η δ q) := TLat.mono (h1 q (by omega) a ha) (Err_ge hη (hle d1 (by simp)) q hq1)
  have tl1 : TLat q a 1 (Err η δ q) := TLat.mono (h2 q (by omega) a ha) (Err_ge hη (hle d2 (by simp)) q hq1)
  have tl2 : TLat q a 2 (Err η δ q) := TLat.mono (h3 q (by omega) a ha) (Err_ge hη (hle d3 (by simp)) q hq1)
  have tl3 : TLat q a 3 (Err η δ q) := TLat.mono (h4 q (by omega) a ha) (Err_ge hη (hle d4 (by simp)) q hq1)
  have tl4 : TLat q a 4 (Err η δ q) := TLat.mono (h5 q (by omega) a ha) (Err_ge hη (hle d5 (by simp)) q hq1)
  have tl5 : TLat q a 5 (Err η δ q) := TLat.mono (h6 q (by omega) a ha) (Err_ge hη (hle d6 (by simp)) q hq1)
  have tu1 : TUat q a 1 (Err η δ q) := TUat.mono (h7 q (by omega) a ha) (Err_ge hη (hle d7 (by simp)) q hq1)
  have tu2 : TUat q a 2 (Err η δ q) := TUat.mono (h8 q (by omega) a ha) (Err_ge hη (hle d8 (by simp)) q hq1)
  have tu3 : TUat q a 3 (Err η δ q) := TUat.mono (h9 q (by omega) a ha) (Err_ge hη (hle d9 (by simp)) q hq1)
  have tu4 : TUat q a 4 (Err η δ q) := TUat.mono (h10 q (by omega) a ha) (Err_ge hη (hle d10 (by simp)) q hq1)
  have tu5 : TUat q a 5 (Err η δ q) := TUat.mono (h11 q (by omega) a ha) (Err_ge hη (hle d11 (by simp)) q hq1)
  have tu6 : TUat q a 6 (Err η δ q) := TUat.mono (h12 q (by omega) a ha) (Err_ge hη (hle d12 (by simp)) q hq1)
  have tr1 : TRat q a 1 (Err η δ q) := TRat.mono (h13 q (by omega) a ha) (Err_ge hη (hle d13 (by simp)) q hq1)
  have tr2 : TRat q a 2 (Err η δ q) := TRat.mono (h14 q (by omega) a ha) (Err_ge hη (hle d14 (by simp)) q hq1)
  have tr3 : TRat q a 3 (Err η δ q) := TRat.mono (h15 q (by omega) a ha) (Err_ge hη (hle d15 (by simp)) q hq1)
  have tr4 : TRat q a 4 (Err η δ q) := TRat.mono (h16 q (by omega) a ha) (Err_ge hη (hle d16 (by simp)) q hq1)
  have tr5 : TRat q a 5 (Err η δ q) := TRat.mono (h17 q (by omega) a ha) (Err_ge hη (hle d17 (by simp)) q hq1)
  have p0 : P6at q a 0 (Err η δ q) := P6at.mono (h18 q (by omega) a ha) (Err_ge' (η := η) (hle d18 (by simp)) q hq1)
  have p1 : P6at q a 1 (Err η δ q) := P6at.mono (h19 q (by omega) a ha) (Err_ge' (η := η) (hle d19 (by simp)) q hq1)
  have p2 : P6at q a 2 (Err η δ q) := P6at.mono (h20 q (by omega) a ha) (Err_ge' (η := η) (hle d20 (by simp)) q hq1)
  have p3 : P6at q a 3 (Err η δ q) := P6at.mono (h21 q (by omega) a ha) (Err_ge' (η := η) (hle d21 (by simp)) q hq1)
  have p4 : P6at q a 4 (Err η δ q) := P6at.mono (h22 q (by omega) a ha) (Err_ge' (η := η) (hle d22 (by simp)) q hq1)
  have p5 : P6at q a 5 (Err η δ q) := P6at.mono (h23 q (by omega) a ha) (Err_ge' (η := η) (hle d23 (by simp)) q hq1)
  have p6 : P6at q a 6 (Err η δ q) := P6at.mono (h24 q (by omega) a ha) (Err_ge' (η := η) (hle d24 (by simp)) q hq1)
  have p7 : P6at q a 7 (Err η δ q) := P6at.mono (h25 q (by omega) a ha) (Err_ge' (η := η) (hle d25 (by simp)) q hq1)
  have ib2 := fun f hf ho =>
    (h26 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d26 (by simp)) q hq1)
  have ib3 := fun f hf ho =>
    (h27 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d27 (by simp)) q hq1)
  have ib4 := fun f hf ho =>
    (h28 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d28 (by simp)) q hq1)
  have ib5 := fun f hf ho =>
    (h29 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d29 (by simp)) q hq1)
  have ib6 := fun f hf ho =>
    (h30 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d30 (by simp)) q hq1)
  have ib7 := fun f hf ho =>
    (h31 q (by omega) a ha f hf ho).mono (Err_ge' (η := η) (hle d31 (by simp)) q hq1)
  refine ⟨hLq, ⟨lf_j0 hLq p0, fun i hi hW => lf_e1 hLq tl0 hi hW, fun i hi _ => lf_p1 hLq p1 hi,
    fun i hi j hj _ hd => lf_e2 hLq hE0 tu1 hi hj (ok2_of_dec2 hd),
    fun i hi j hj _ hd => lf_p2 hLq p2 hi hj (ok2_of_dec2 hd) fun hib =>
      ib2 _ (Finset.mem_image.2 ⟨(i, j), by simp [hi, hj], rfl⟩) (by simpa [List.ofFn_succ] using hib),
    fun i hi _ j hj _ hs => lf_e2' hLq tl1 tr1 hi hj hs,
    fun i hi j hj _ hd k hk hkk hn3 => lf_e3 hLq hE0 tu2 hi hj hk (ok3_of_dec2 hd hk hkk hn3),
    fun i hi j hj _ hd k hk hkk hn3 => lf_p3 hLq p3 hi hj hk (ok3_of_dec2 hd hk hkk hn3) fun hib =>
      ib3 _ (Finset.mem_image.2 ⟨(i, j, k), by simp [hi, hj, hk], rfl⟩) (by simpa [List.ofFn_succ] using hib),
    fun i hi j hj _ _ k hk _ hn3 => lf_e3' hLq tl2 tr2 hi hj hk hn3,
    fun i hi j hj _ _ k hk _ _ l hl _ hs => lf_e4 hLq tl3 tr3 hi hj hk (by omega) hs,
    fun i j k l hD => lf_e4gt hLq hE0 tu3 (deep'_idx hD) (ok4_of_dec4 hD.2.2.2),
    fun i j k l hD => lf_p4 hLq p4 (deep'_idx hD) (ok4_of_dec4 hD.2.2.2) fun hib => by
      obtain ⟨hi, hj, hk, hl⟩ := deep'_idx hD
      exact ib4 _ (Finset.mem_image.2 ⟨(i, j, k, l), by simp [hi, hj, hk, hl], rfl⟩)
        (by simpa [List.ofFn_succ] using hib),
    fun i j k l hD b hb hK hn => lf_e5gt hLq hE0 tu4 (deep'_idx hD) hb (ok5_of_dec4 hD.2.2.2 hb hK hn),
    fun i j k l hD b hb hK hn => lf_p5 hLq p5 (deep'_idx hD) hb (ok5_of_dec4 hD.2.2.2 hb hK hn) fun hib => by
      obtain ⟨hi, hj, hk, hl⟩ := deep'_idx hD
      exact ib5 _ (Finset.mem_image.2 ⟨(i, j, k, l, b), by simp [hi, hj, hk, hl, hb], rfl⟩)
        (by simpa [List.ofFn_succ] using hib),
    fun i j k l hD b hb _ hn => lf_e5' hLq tl4 tr4 (deep'_idx hD) hb hn,
    fun i j k l hD b hb _ _ c hc _ hs => lf_e6 hLq tl5 tr5 (deep'_idx hD) hb (by omega) hs,
    fun i j k l b c hD => lf_e6gt hLq hE0 tu5 (deep'_idx hD.1) hD.2.1 (by have := hD.2.2.2.2.1; have := hD.2.1; omega)
      (ok6_of_allowed6R (Scheme8.allowed6 hD.2.2.2.2.2.2)),
    fun i j k l b c hD => lf_p6 hLq p6 (deep'_idx hD.1) hD.2.1 (by have := hD.2.2.2.2.1; have := hD.2.1; omega)
      (ok6_of_allowed6R (Scheme8.allowed6 hD.2.2.2.2.2.2)) fun hib => by
        obtain ⟨hi, hj, hk, hl⟩ := deep'_idx hD.1
        have hb := hD.2.1
        have hc : c < nC := by have := hD.2.2.2.2.1; omega
        exact ib6 _ (Finset.mem_image.2 ⟨(i, j, k, l, b, c), by simp [hi, hj, hk, hl, hb, hc], rfl⟩)
          (by simpa [List.ofFn_succ] using hib),
    fun i j k l b c hD d hd hK => by
      have hc : c < nC := by have := hD.2.2.2.2.1; have := hD.2.1; omega
      have hdn : d < nC := by omega
      exact lf_e7gt hLq hE0 tu6 (deep'_idx hD.1) hD.2.1 hc hdn
        (ok7_of_allowed6R (Scheme8.allowed6 hD.2.2.2.2.2.2) hdn hK),
    fun i j k l b c hD d hd hK => by
      have hc : c < nC := by have := hD.2.2.2.2.1; have := hD.2.1; omega
      have hdn : d < nC := by omega
      refine lf_p7 hLq p7 (deep'_idx hD.1) hD.2.1 hc hdn (ok7_of_allowed6R (Scheme8.allowed6 hD.2.2.2.2.2.2) hdn hK)
        fun hib => ?_
      obtain ⟨hi, hj, hk, hl⟩ := deep'_idx hD.1
      have hb := hD.2.1
      exact ib7 _ (Finset.mem_image.2 ⟨(i, j, k, l, b, c, d), by simp [hi, hj, hk, hl, hb, hc, hdn], rfl⟩)
        (by simpa [List.ofFn_succ] using hib)⟩⟩

end SieveQ8
