/-
# The dropped terms' `B`-count, to depth 8

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK`, `GridOKC`, `Fits`); the
certificate is `SieveDeepDefs.lean`'s and the decomposition that of `SieveBuch8.lean` under the bilinear rule with the
certificate's scheme of decisions (`SieveDeep.scheme`), on a grid with `HC = 4H` (`hHC`) and `4H + 4HC ≤ V`
(`hfit8`), which keeps the boxes of depth 8 inside `DEN`.

* `famI_le_SB`, `drop4_le'`, `drop6_le'`, `drop8_le`: a dropped cell's `B`-count is at most `φ(q)⁻¹` times its box's
  sum `SieveRough.SB` over the primes of its cells.
* `trB_le_trapF`, `exB_le_lastF`: the fixed-point factors bound the reals they round up, `trB ≤ trapF/SC` and
  `exB ≤ lastF/SC`.
* `share4D`, `share6D`, `share8D`: **the shares of the dropped cells**, by `SieveRough.shareBox`: for every `δ > 0`,
  eventually the box's sum is at most its charge `/(SC⁸K) + δ`, times `x/log x` (a counted cell of depth 4 at
  `P3·Q4·SC⁴`, of depth 6 at `P3·trapF·trapF·q6·SC²`, a cell of depth 8 of the region at its factors' product).
* `DeepGrid`, `schemeD`: a grid with `HC = 4H`, `H > 0` and `4H + 4HC ≤ V`, and the certificate's scheme on it.
* `dT8` … `dT3`, `dT`: the dropped cells' sums below a cell `(i, j)`, and `E8_le` … `E3_le`, `E1_le`: the
  decomposition's dropped terms are at most `φ(q)⁻¹` times them, plus the corner's `n²|cornerP|²`.
* `dT_le_cost`: given the shares of a cell's dropped cells at `x`, `dT ≤ (costD/K)X + δ'·M·X` with
  `M = 1 + n²(1 + nC²(nC² + 1))`, level by level (`sum_level`) against the charges `SieveDeep.Ch8` … `Ch3`, and
  `Ch3 ≤ SC⁸·refcost` (`SieveDeep.Ch3_le`).
* `shares_ev8`, `drop_ev8`: **the dropped terms, for large `q`**: if `totalD/K ≤ c` in the reals, then for `ε > 0`,
  `E1(g_B) ≤ φ(q)⁻¹(c + ε)x/log x`, as `SieveDrop.drop_ev_of`.

The file imports `SieveDeepCost.lean`, `SieveBox.lean` and `SieveDrop.lean`.
-/
import SieveDeepCost
import SieveBox
import SieveDrop

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveRoute SieveDeep
open SieveCert (V DEN H U1 U2 cand inKK ne3 counted4 surelyEval cell bound2 K nC eC HC cellC inKK5 ne5 counted6 Gc
  omKw)

namespace SieveDrop8

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-! ### The dropped cells' boxes -/

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- A family whose tuples lie in a box's intervals has `B`-count at most `φ(q)⁻¹ SB`. -/
theorem famI_le_SB {q : ℕ} (hq : 1 ≤ q) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) (hF : ∀ rt ∈ F, ∀ t, (rt t).Prime)
    (a w : Fin (k' + 1) → ℕ) (hbox : ∀ rt ∈ F, ∀ t, rt t ∈ boxP (xq q) (a t) (w t)) :
    famI (gB q) (N1 q) (N2 q) F ≤ (q.totient : ℝ)⁻¹ * SB (xq q) a w := by
  refine (SieveDrop.famI_gB_le q F hF hq).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun rt hrt => Fintype.mem_piFinset.2 (hbox rt hrt))
    (fun _ _ _ => Nat.cast_nonneg _)

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem mem_boxP_of {x : ℝ} {c p : ℕ} (hp : p.Prime) (h : InC x c p) : p ∈ boxP x (SieveCert.e c) H :=
  mem_primesIn.2 ⟨hp, h.1, h.2⟩

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem mem_boxPC_of {x : ℝ} {c p : ℕ} (hp : p.Prime) (h : InCC x c p) : p ∈ boxP x (eC c) HC :=
  mem_primesIn.2 ⟨hp, h.1, h.2⟩

/-- The box of a cell of depth 4: its lower ends. -/
def a4 (i j k l : ℕ) : Fin 4 → ℕ := ![SieveCert.e i, SieveCert.e j, SieveCert.e k, SieveCert.e l]
/-- The box of a cell of depth 4: its widths. -/
def w4 : Fin 4 → ℕ := ![H, H, H, H]
/-- The box of a cell of depth 6: its lower ends. -/
def a6 (i j k l b c : ℕ) : Fin 6 → ℕ := ![SieveCert.e i, SieveCert.e j, SieveCert.e k, SieveCert.e l, eC b, eC c]
/-- The box of a cell of depth 6: its widths. -/
def w6 : Fin 6 → ℕ := ![H, H, H, H, HC, HC]
/-- The box of a cell of depth 8: its lower ends. -/
def a8 (i j k l b c d f : ℕ) : Fin 8 → ℕ :=
  ![SieveCert.e i, SieveCert.e j, SieveCert.e k, SieveCert.e l, eC b, eC c, eC d, eC f]
/-- The box of a cell of depth 8: its widths. -/
def w8 : Fin 8 → ℕ := ![H, H, H, H, HC, HC, HC, HC]

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A dropped cell of depth 4**: its `B`-count is at most `φ(q)⁻¹ SB` over its box. -/
theorem drop4_le' {q : ℕ} (hq : 1 ≤ q) (i j k l : ℕ) :
    (parQ q).I (gB q) ((parQ q).S4c i j k l) ≤ (q.totient : ℝ)⁻¹ * SB (xq q) (a4 i j k l) w4 := by
  have hF : ∀ rt ∈ famSet 4 (N2 q) ((parQ q).S4c i j k l), ∀ t, (rt t).Prime :=
    fun rt hrt t => ((mem_famSet.1 hrt).1 t).2
  refine famI_le_SB hq _ hF _ _ fun rt hrt t => ?_
  obtain ⟨-, hi, hj, hk, hl, -⟩ := (parQ q).facts_S4c hrt
  fin_cases t
  · exact mem_boxP_of (hF rt hrt 0) hi
  · exact mem_boxP_of (hF rt hrt 1) hj
  · exact mem_boxP_of (hF rt hrt 2) hk
  · exact mem_boxP_of (hF rt hrt 3) hl

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A dropped cell of depth 6**: its `B`-count is at most `φ(q)⁻¹ SB` over its box. -/
theorem drop6_le' {q : ℕ} (hq : 1 ≤ q) (i j k l b c : ℕ) :
    (parQ q).I (gB q) ((parQ q).S6c i j k l b c) ≤ (q.totient : ℝ)⁻¹ * SB (xq q) (a6 i j k l b c) w6 := by
  have hF : ∀ rt ∈ famSet 6 (N2 q) ((parQ q).S6c i j k l b c), ∀ t, (rt t).Prime :=
    fun rt hrt t => ((mem_famSet.1 hrt).1 t).2
  refine famI_le_SB hq _ hF _ _ fun rt hrt t => ?_
  obtain ⟨-, hi, hj, hk, hl, hb, hc, -⟩ := (parQ q).facts_S6c hrt
  fin_cases t
  · exact mem_boxP_of (hF rt hrt 0) hi
  · exact mem_boxP_of (hF rt hrt 1) hj
  · exact mem_boxP_of (hF rt hrt 2) hk
  · exact mem_boxP_of (hF rt hrt 3) hl
  · exact mem_boxPC_of (hF rt hrt 4) hb
  · exact mem_boxPC_of (hF rt hrt 5) hc

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A dropped cell of depth 8**: its `B`-count is at most `φ(q)⁻¹ SB` over its box. -/
theorem drop8_le {q : ℕ} (hq : 1 ≤ q) (i j k l b c d f : ℕ) :
    (parQ q).I (gB q) ((parQ q).S8c i j k l b c d f) ≤ (q.totient : ℝ)⁻¹ * SB (xq q) (a8 i j k l b c d f) w8 := by
  have hF : ∀ rt ∈ famSet 8 (N2 q) ((parQ q).S8c i j k l b c d f), ∀ t, (rt t).Prime :=
    fun rt hrt t => ((mem_famSet.1 hrt).1 t).2
  refine famI_le_SB hq _ hF _ _ fun rt hrt t => ?_
  obtain ⟨-, hi, hj, hk, hl, hb, hc, hd, hf, -⟩ := (parQ q).facts_S8c hrt
  fin_cases t
  · exact mem_boxP_of (hF rt hrt 0) hi
  · exact mem_boxP_of (hF rt hrt 1) hj
  · exact mem_boxP_of (hF rt hrt 2) hk
  · exact mem_boxP_of (hF rt hrt 3) hl
  · exact mem_boxPC_of (hF rt hrt 4) hb
  · exact mem_boxPC_of (hF rt hrt 5) hc
  · exact mem_boxPC_of (hF rt hrt 6) hd
  · exact mem_boxPC_of (hF rt hrt 7) hf

/-! ### The fixed-point factors -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem SC_pos : (0 : ℝ) < SC := by unfold SC; positivity

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- `trB ≤ trapF/SC`. -/
theorem trB_le_trapF {a w : ℕ} (ha : 0 < a) : SieveCert.trB a w ≤ (trapF a w : ℝ) / SC := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := SieveOmegaB.div_le_cdiv (SC * w * (2 * a + w)) (2 * a * (a + w)) (by positivity)
  rw [le_div_iff₀ SC_pos]
  unfold trapF
  unfold SieveCert.trB
  push_cast at h ⊢
  calc (w : ℝ) * (2 * a + w) / (2 * a * (a + w)) * SC = SC * w * (2 * a + w) / (2 * a * (a + w)) := by ring
    _ ≤ _ := h

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- `exB ≤ lastF/SC`. -/
theorem exB_le_lastF {a w : ℕ} (ha : 0 < a) : SieveCert.exB a w ≤ (lastF a w : ℝ) / SC := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h := SieveOmegaB.div_le_cdiv (SC * w * DEN) (a * (a + w)) (by positivity)
  rw [le_div_iff₀ SC_pos]
  unfold lastF
  unfold SieveCert.exB
  push_cast at h ⊢
  calc (DEN : ℝ) * w / (a * (a + w)) * SC = SC * w * DEN / (a * (a + w)) := by ring
    _ ≤ _ := h

/-! ### The shares of the dropped cells -/

omit [Route] [RouteOK] [Fits] in
/-- **The share of a counted cell of depth 4**, at its charge `P3·Q4·SC⁴`. -/
theorem share4D {i j k l : ℕ} (h : counted4 i j k l = true) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, SB x (a4 i j k l) w4 ≤
      (((P3 i j k * (Q4 (i + j + k) l * SC ^ 4) : ℕ) : ℝ) / (SC ^ 8 * K) + δ) * (x / Real.log x) := by
  have hpos := SieveCert.e_pos
  have hH := SieveCert.H_pos
  have h4H := SieveCert.GridOK.four_H_le_V
  have hV : SieveCert.V ≤ SieveCert.e l := by unfold SieveCert.e; omega
  unfold counted4 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : ∑ t : Fin 3, a4 i j k l t.castSucc = 3 * V + H * (i + j + k) := by
    simp [a4, Fin.sum_univ_succ, e_eq]; ring
  have hw : ∑ t, w4 t = 4 * H := by simp [w4, Fin.sum_univ_succ]; ring
  refine shareBox (a4 i j k l) w4 (fun t => by fin_cases t <;> exact hpos _) ?_ ?_ hδ
  · rw [hs, hw, show a4 i j k l (Fin.last 3) = SieveCert.e l from rfl]
    have := e_eq i; have := e_eq j; have := e_eq k
    nlinarith [h.1]
  · rw [hs, hw, show a4 i j k l (Fin.last 3) = SieveCert.e l from rfl, show w4 (Fin.last 3) = H from rfl]
    have hprod : ∏ t : Fin 3, SieveCert.trB (a4 i j k l t.castSucc) (w4 t.castSucc) =
        SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H * SieveCert.trB (SieveCert.e k) H := by
      simp [Fin.prod_univ_three, a4, w4]
    rw [hprod]
    have hK := SieveCert.K_pos'
    have hS := SC_pos
    have t1 := trB_le_trapF (w := H) (hpos i)
    have t2 := trB_le_trapF (w := H) (hpos j)
    have t3 := trB_le_trapF (w := H) (hpos k)
    have t4 := exB_le_lastF (w := H) (hpos l)
    have n1 := SieveCert.trB_nonneg (SieveCert.e i) H
    have n2 := SieveCert.trB_nonneg (SieveCert.e j) H
    have n3 := SieveCert.trB_nonneg (SieveCert.e k) H
    have n4 := SieveCert.exB_nonneg (SieveCert.e l) H
    calc (omKw (3 * V + H * (i + j + k)) (SieveCert.e l) (4 * H) H : ℝ) / K *
          (SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H * SieveCert.trB (SieveCert.e k) H *
            SieveCert.exB (SieveCert.e l) H)
        ≤ (omKw (3 * V + H * (i + j + k)) (SieveCert.e l) (4 * H) H : ℝ) / K *
          ((trapF (SieveCert.e i) H : ℝ) / SC * ((trapF (SieveCert.e j) H : ℝ) / SC) *
            ((trapF (SieveCert.e k) H : ℝ) / SC) * ((lastF (SieveCert.e l) H : ℝ) / SC)) := by gcongr
      _ = _ := by
          unfold P3 Q4
          push_cast
          field_simp

omit [Route] [RouteOK] [Fits] in
/-- **The share of a counted cell of depth 6**, at its charge `P3·trapF·trapF·q6·SC²`, for `HC = 4H`. -/
theorem share6D [SieveCert.GridOKC] (hHC : HC = 4 * H) {i j k l b c : ℕ} (h : counted6 i j k l b c = true) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, SB x (a6 i j k l b c) w6 ≤
      (((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * (q6 (i + j + k + l + 4 * b) c * SC * SC) : ℕ) :
        ℝ) / (SC ^ 8 * K) + δ) * (x / Real.log x) := by
  have hpos := SieveCert.e_pos
  have hposC : ∀ b, 0 < eC b := @SieveCert.e_pos Gc SieveCert.GridOKC.ok
  have hH := SieveCert.H_pos
  have hfit := SieveCert.GridOKC.fit
  have hV : SieveCert.V ≤ eC c := by rw [eC_eq]; omega
  unfold counted6 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : ∑ t : Fin 5, a6 i j k l b c t.castSucc = 5 * V + H * (i + j + k + l + 4 * b) := by
    simp [a6, Fin.sum_univ_succ, e_eq, eC_eq, hHC]; ring
  have hw : ∑ t, w6 t = 4 * H + 2 * HC := by simp [w6, Fin.sum_univ_succ]; ring
  refine shareBox (a6 i j k l b c) w6 (fun t => by fin_cases t <;> first | exact hpos _ | exact hposC _) ?_ ?_ hδ
  · rw [hs, hw, show a6 i j k l b c (Fin.last 5) = eC c from rfl]
    have h1 := h.1
    simp only [e_eq, eC_eq, hHC] at h1 ⊢
    rw [hHC] at hfit
    have : 0 ≤ H * c := Nat.zero_le _
    nlinarith
  · rw [hs, hw, show a6 i j k l b c (Fin.last 5) = eC c from rfl, show w6 (Fin.last 5) = HC from rfl]
    have hprod : ∏ t : Fin 5, SieveCert.trB (a6 i j k l b c t.castSucc) (w6 t.castSucc) =
        SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H * SieveCert.trB (SieveCert.e k) H *
          SieveCert.trB (SieveCert.e l) H * SieveCert.trB (eC b) HC := by
      simp [Fin.prod_univ_succ, a6, w6]; ring
    rw [hprod]
    have hK := SieveCert.K_pos'
    have hS := SC_pos
    have t1 := trB_le_trapF (w := H) (hpos i)
    have t2 := trB_le_trapF (w := H) (hpos j)
    have t3 := trB_le_trapF (w := H) (hpos k)
    have t4 := trB_le_trapF (w := H) (hpos l)
    have t5 := trB_le_trapF (w := HC) (hposC b)
    have t6 := exB_le_lastF (w := HC) (hposC c)
    have n1 := SieveCert.trB_nonneg (SieveCert.e i) H
    have n2 := SieveCert.trB_nonneg (SieveCert.e j) H
    have n3 := SieveCert.trB_nonneg (SieveCert.e k) H
    have n4 := SieveCert.trB_nonneg (SieveCert.e l) H
    have n5 := SieveCert.trB_nonneg (eC b) HC
    have n6 := SieveCert.exB_nonneg (eC c) HC
    calc (omKw (5 * V + H * (i + j + k + l + 4 * b)) (eC c) (4 * H + 2 * HC) HC : ℝ) / K *
          (SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H * SieveCert.trB (SieveCert.e k) H *
            SieveCert.trB (SieveCert.e l) H * SieveCert.trB (eC b) HC * SieveCert.exB (eC c) HC)
        ≤ (omKw (5 * V + H * (i + j + k + l + 4 * b)) (eC c) (4 * H + 2 * HC) HC : ℝ) / K *
          ((trapF (SieveCert.e i) H : ℝ) / SC * ((trapF (SieveCert.e j) H : ℝ) / SC) *
            ((trapF (SieveCert.e k) H : ℝ) / SC) * ((trapF (SieveCert.e l) H : ℝ) / SC) *
            ((trapF (eC b) HC : ℝ) / SC) * ((lastF (eC c) HC : ℝ) / SC)) := by gcongr
      _ = _ := by
          unfold P3 q6
          push_cast
          field_simp

omit [Route] [RouteOK] [Fits] in
/-- **The share of a cell of depth 8 of the region**, at the product of its factors, for `HC = 4H` and
`4H + 4HC ≤ V`. -/
theorem share8D [SieveCert.GridOKC] (hHC : HC = 4 * H) (hfit8 : 4 * H + 4 * HC ≤ V) {i j k l b c d f : ℕ}
    (h : SieveBuch.reg8 i j k l b c d f = true) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, SB x (a8 i j k l b c d f) w8 ≤
      (((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC * trapF (eC d) HC *
        (lastF (eC f) HC * omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f) (4 * H + 4 * HC) HC) :
          ℕ) : ℝ) / (SC ^ 8 * K) + δ) * (x / Real.log x) := by
  have hpos := SieveCert.e_pos
  have hposC : ∀ b, 0 < eC b := @SieveCert.e_pos Gc SieveCert.GridOKC.ok
  have hH := SieveCert.H_pos
  have hV : SieveCert.V ≤ eC f := by rw [eC_eq]; omega
  unfold SieveBuch.reg8 at h
  simp only [decide_eq_true_eq] at h
  have hs : ∑ t : Fin 7, a8 i j k l b c d f t.castSucc = 7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d) := by
    simp [a8, Fin.sum_univ_succ, e_eq, eC_eq, hHC]; ring
  have hw : ∑ t, w8 t = 4 * H + 4 * HC := by simp [w8, Fin.sum_univ_succ]; ring
  refine shareBox (a8 i j k l b c d f) w8 (fun t => by fin_cases t <;> first | exact hpos _ | exact hposC _) ?_ ?_ hδ
  · rw [hs, hw, show a8 i j k l b c d f (Fin.last 7) = eC f from rfl]
    have h1 := h
    simp only [e_eq, eC_eq, hHC] at h1 ⊢
    rw [hHC] at hfit8
    have : 0 ≤ H * f := Nat.zero_le _
    nlinarith
  · rw [hs, hw, show a8 i j k l b c d f (Fin.last 7) = eC f from rfl, show w8 (Fin.last 7) = HC from rfl]
    have hprod : ∏ t : Fin 7, SieveCert.trB (a8 i j k l b c d f t.castSucc) (w8 t.castSucc) =
        SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H * SieveCert.trB (SieveCert.e k) H *
          SieveCert.trB (SieveCert.e l) H * SieveCert.trB (eC b) HC * SieveCert.trB (eC c) HC *
            SieveCert.trB (eC d) HC := by
      simp [Fin.prod_univ_succ, a8, w8]; ring
    rw [hprod]
    have hK := SieveCert.K_pos'
    have hS := SC_pos
    have t1 := trB_le_trapF (w := H) (hpos i)
    have t2 := trB_le_trapF (w := H) (hpos j)
    have t3 := trB_le_trapF (w := H) (hpos k)
    have t4 := trB_le_trapF (w := H) (hpos l)
    have t5 := trB_le_trapF (w := HC) (hposC b)
    have t6 := trB_le_trapF (w := HC) (hposC c)
    have t7 := trB_le_trapF (w := HC) (hposC d)
    have t8 := exB_le_lastF (w := HC) (hposC f)
    have n1 := SieveCert.trB_nonneg (SieveCert.e i) H
    have n2 := SieveCert.trB_nonneg (SieveCert.e j) H
    have n3 := SieveCert.trB_nonneg (SieveCert.e k) H
    have n4 := SieveCert.trB_nonneg (SieveCert.e l) H
    have n5 := SieveCert.trB_nonneg (eC b) HC
    have n6 := SieveCert.trB_nonneg (eC c) HC
    have n7 := SieveCert.trB_nonneg (eC d) HC
    have n8 := SieveCert.exB_nonneg (eC f) HC
    calc (omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f) (4 * H + 4 * HC) HC : ℝ) / K *
          (SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H * SieveCert.trB (SieveCert.e k) H *
            SieveCert.trB (SieveCert.e l) H * SieveCert.trB (eC b) HC * SieveCert.trB (eC c) HC *
            SieveCert.trB (eC d) HC * SieveCert.exB (eC f) HC)
        ≤ (omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f) (4 * H + 4 * HC) HC : ℝ) / K *
          ((trapF (SieveCert.e i) H : ℝ) / SC * ((trapF (SieveCert.e j) H : ℝ) / SC) *
            ((trapF (SieveCert.e k) H : ℝ) / SC) * ((trapF (SieveCert.e l) H : ℝ) / SC) *
            ((trapF (eC b) HC : ℝ) / SC) * ((trapF (eC c) HC : ℝ) / SC) * ((trapF (eC d) HC : ℝ) / SC) *
            ((lastF (eC f) HC : ℝ) / SC)) := by
          have p4 : SieveCert.trB (SieveCert.e i) H * SieveCert.trB (SieveCert.e j) H *
              SieveCert.trB (SieveCert.e k) H * SieveCert.trB (SieveCert.e l) H ≤
              (trapF (SieveCert.e i) H : ℝ) / SC * ((trapF (SieveCert.e j) H : ℝ) / SC) *
                ((trapF (SieveCert.e k) H : ℝ) / SC) * ((trapF (SieveCert.e l) H : ℝ) / SC) := by gcongr
          have hy : ∀ m : ℕ, (0 : ℝ) ≤ (m : ℝ) / SC := fun m => div_nonneg (Nat.cast_nonneg _) hS.le
          have q4 := mul_nonneg (mul_nonneg (mul_nonneg (hy (trapF (SieveCert.e i) H)) (hy (trapF (SieveCert.e j) H)))
            (hy (trapF (SieveCert.e k) H))) (hy (trapF (SieveCert.e l) H))
          have p5 := mul_le_mul p4 t5 n5 q4
          have p6 := mul_le_mul p5 t6 n6 (mul_nonneg q4 (hy _))
          have p7 := mul_le_mul p6 t7 n7 (mul_nonneg (mul_nonneg q4 (hy _)) (hy _))
          have p8 := mul_le_mul p7 t8 n8 (mul_nonneg (mul_nonneg (mul_nonneg q4 (hy _)) (hy _)) (hy _))
          exact mul_le_mul_of_nonneg_left p8 (div_nonneg (Nat.cast_nonneg _) hK.le)
      _ = _ := by
          unfold P3
          push_cast
          ring

/-! ### The certificate's grid and its scheme -/

/-- **A grid of the certificate to depth 8**: `HC = 4H`, `H > 0` and `4H + 4HC ≤ V`, each checked by `decide` for a
given grid. -/
class DeepGrid [SieveCert.Grid] : Prop where
  hHC : HC = 4 * H
  hH : 0 < H
  fit8 : 4 * H + 4 * HC ≤ V

attribute [local instance] SieveCert.ibRule

/-- The certificate's scheme of decisions, on a grid of the certificate, under the bilinear rule. -/
@[instance_reducible] instance schemeD [SieveCert.IBPar] [DeepGrid] : SieveBuch.Scheme8 :=
  scheme DeepGrid.hHC DeepGrid.hH

section Drops

variable [SieveCert.IBPar] [DeepGrid]

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem dec2_eq (i j : ℕ) : SieveBuch.Scheme8.dec2 i j = decD i j := rfl
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem dec4_eq (i j k l : ℕ) : SieveBuch.Scheme8.dec4 i j k l = dec4D i j k l := rfl
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem dec6_eq (i j k l b c : ℕ) : SieveBuch.Scheme8.dec6 i j k l b c = dec6D i j k l b c := rfl

/-! ### The dropped cells' sums -/

/-- The sums of the cells of depth 8 of the region below `(i, j, k, l, b, c, d)`. -/
noncomputable def dT8 (x : ℝ) (i j k l b c d : ℕ) : ℝ :=
  ∑ f ∈ range (d + 1), if SieveBuch.reg8 i j k l b c d f = true then SB x (a8 i j k l b c d f) w8 else 0

/-- The dropped sums below a decomposed cell `(i, j, k, l, b, c)` of depth 6. -/
noncomputable def dT7 (x : ℝ) (i j k l b c : ℕ) : ℝ :=
  ∑ d ∈ range (c + 1), if SieveBuch.inKK7 i j k l b c d = true then dT8 x i j k l b c d else 0

/-- The dropped sums of depths 6 to 8 below `(i, j, k, l, b)`. -/
noncomputable def dT6 (x : ℝ) (i j k l b : ℕ) : ℝ :=
  ∑ c ∈ range (b + 1), if counted6 i j k l b c = true then
    (if dec6D i j k l b c = true then dT7 x i j k l b c else SB x (a6 i j k l b c) w6) else 0

/-- The dropped sums below a decomposed cell `(i, j, k, l)` of depth 4. -/
noncomputable def dT5 (x : ℝ) (i j k l : ℕ) : ℝ :=
  ∑ b ∈ range nC, if inKK5 i j k l b = true ∧ ne5 i j k l b = true then dT6 x i j k l b else 0

/-- The dropped sums of the row `(i, j, k)`. -/
noncomputable def dT4 (x : ℝ) (i j k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), if counted4 i j k l = true then
    (if dec4D i j k l = true then dT5 x i j k l else SB x (a4 i j k l) w4) else 0

/-- The dropped sums below a decomposed cell `(i, j)`. -/
noncomputable def dT3 (x : ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ range SieveCert.n, if inKK i j k = true ∧ ne3 i j k = true then dT4 x i j k else 0

/-- **The dropped sums of the cell `(i, j)`**: itself when it is a candidate not decomposed, those below it when
decomposed. -/
noncomputable def dT (x : ℝ) (i j : ℕ) : ℝ :=
  (if cand i j = true ∧ decD i j = false then SieveDrop.S2 x i j else 0) +
    (if cand i j = true ∧ decD i j = true then dT3 x i j else 0)

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [DeepGrid] in
theorem dT8_nonneg (x : ℝ) (i j k l b c d : ℕ) : 0 ≤ dT8 x i j k l b c d :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact le_rfl | exact SB_nonneg _ _ _
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [DeepGrid] in
theorem dT7_nonneg (x : ℝ) (i j k l b c : ℕ) : 0 ≤ dT7 x i j k l b c :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact le_rfl | exact dT8_nonneg _ _ _ _ _ _ _ _
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [DeepGrid] in
theorem dT6_nonneg (x : ℝ) (i j k l b : ℕ) : 0 ≤ dT6 x i j k l b :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs <;> first | exact le_rfl | exact dT7_nonneg _ _ _ _ _ _ _ | exact SB_nonneg _ _ _
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [DeepGrid] in
theorem dT5_nonneg (x : ℝ) (i j k l : ℕ) : 0 ≤ dT5 x i j k l :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact le_rfl | exact dT6_nonneg _ _ _ _ _ _
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [DeepGrid] in
theorem dT4_nonneg (x : ℝ) (i j k : ℕ) : 0 ≤ dT4 x i j k :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs <;> first | exact le_rfl | exact dT5_nonneg _ _ _ _ _ | exact SB_nonneg _ _ _
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [DeepGrid] in
theorem dT3_nonneg (x : ℝ) (i j : ℕ) : 0 ≤ dT3 x i j :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact le_rfl | exact dT4_nonneg _ _ _ _
omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [DeepGrid] in
theorem dT_nonneg (x : ℝ) (i j : ℕ) : 0 ≤ dT x i j := by
  unfold dT
  refine add_nonneg ?_ ?_ <;> split_ifs <;>
    first | exact le_rfl | exact SieveDrop.S2_nonneg _ _ _ | exact dT3_nonneg _ _ _

/-! ### The dropped terms against the dropped sums -/

omit [RouteOK] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [DeepGrid] in
theorem E8_le {q : ℕ} (hq : 1 ≤ q) (i j k l b c d : ℕ) :
    (parQ q).E8 (gB q) i j k l b c d ≤ (q.totient : ℝ)⁻¹ * dT8 (xq q) i j k l b c d := by
  unfold Par.E8 dT8
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun f _ => ?_
  split_ifs
  · exact drop8_le hq i j k l b c d f
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [DeepGrid] in
theorem E7_le {q : ℕ} (hq : 1 ≤ q) (i j k l b c : ℕ) :
    (parQ q).E7 (gB q) i j k l b c ≤ (q.totient : ℝ)⁻¹ * dT7 (xq q) i j k l b c := by
  unfold Par.E7 dT7
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  split_ifs
  · exact E8_le hq i j k l b c d
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem E6_le {q : ℕ} (hq : 1 ≤ q) (i j k l b : ℕ) :
    (parQ q).E6 (gB q) i j k l b ≤ (q.totient : ℝ)⁻¹ * dT6 (xq q) i j k l b := by
  unfold Par.E6 dT6
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [dec6_eq]
  split_ifs
  · exact E7_le hq i j k l b c
  · exact drop6_le' hq i j k l b c
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem E5_le {q : ℕ} (hq : 1 ≤ q) (i j k l : ℕ) :
    (parQ q).E5 (gB q) i j k l ≤ (q.totient : ℝ)⁻¹ * dT5 (xq q) i j k l := by
  unfold Par.E5 dT5
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  split_ifs
  · exact E6_le hq i j k l b
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem E4_le {q : ℕ} (hq : 1 ≤ q) (i j k : ℕ) :
    (parQ q).E4 (gB q) i j k ≤ (q.totient : ℝ)⁻¹ * dT4 (xq q) i j k := by
  unfold Par.E4 dT4
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  simp only [dec4_eq]
  split_ifs
  · exact E5_le hq i j k l
  · exact drop4_le' hq i j k l
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem E3_le {q : ℕ} (hq : 1 ≤ q) (i j : ℕ) :
    (parQ q).E3 (gB q) i j ≤ (q.totient : ℝ)⁻¹ * dT3 (xq q) i j := by
  unfold Par.E3 dT3
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs
  · exact E4_le hq i j k
  · exact le_of_eq (mul_zero _).symm

omit [RouteOK] [Fits] in
/-- **The dropped terms' `B`-count**, for `(parQ q).Good`, `z_top² ≤ 4N₁` and `q ≥ 1`: at most
`φ(q)⁻¹(Σ_{i,j} dT + n²|cornerP|²)`. -/
theorem E1_le {q : ℕ} (G : (parQ q).Good) (hsq : (((parQ q).ztop : ℝ)) ^ 2 ≤ 4 * N1 q) (hq : 1 ≤ q) :
    (parQ q).E1 (gB q) ≤ (q.totient : ℝ)⁻¹ * (∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n,
      dT (xq q) i j + (SieveCert.n : ℝ) ^ 2 * ((SieveDrop.cornerP (parQ q).ztop).card : ℝ) ^ 2) := by
  set C := ((SieveDrop.cornerP (parQ q).ztop).card : ℝ) ^ 2 with hC
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hC0 : 0 ≤ C := by positivity
  have hn2 : (SieveCert.n : ℝ) ^ 2 * C = ∑ _i ∈ range SieveCert.n, ∑ _j ∈ range SieveCert.n, C := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hn2, ← Finset.sum_add_distrib, Finset.mul_sum]
  unfold Par.E1
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hi' := Finset.mem_range.1 hi
  by_cases hW : Par.inW i
  · rw [ite_eq_left hW]
    exact Finset.sum_nonneg fun j _ => mul_nonneg hφ (add_nonneg (dT_nonneg _ _ _) hC0)
  rw [ite_eq_right hW]
  unfold Par.E2
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [dec2_eq]
  unfold dT
  have hA : (if (cand i j = true ∧ decD i j = false) ∨ (cand i j = false ∧ Par.sE2 i j = false) then
      (parQ q).I (gB q) ((parQ q).S2c i j) else 0) ≤
        (q.totient : ℝ)⁻¹ * ((if cand i j = true ∧ decD i j = false then SieveDrop.S2 (xq q) i j else 0) + C) := by
    split_ifs with h1 h2
    · exact (SieveDrop.drop2_le hq i j).trans
        (mul_le_mul_of_nonneg_left (by unfold SieveDrop.S2; linarith) hφ)
    · rcases h1 with h1 | h1
      · exact absurd h1 h2
      · refine (SieveDrop.corner_le G hsq hi' hW h1.1 h1.2).trans (mul_le_mul_of_nonneg_left (by linarith) hφ)
    · exact mul_nonneg hφ (add_nonneg (SieveDrop.S2_nonneg _ _ _) hC0)
    · exact mul_nonneg hφ (by linarith)
  have hB : (if cand i j = true ∧ decD i j = true then (parQ q).E3 (gB q) i j else 0) ≤
      (q.totient : ℝ)⁻¹ * (if cand i j = true ∧ decD i j = true then dT3 (xq q) i j else 0) := by
    split_ifs
    · exact E3_le hq i j
    · exact le_of_eq (mul_zero _).symm
  calc _ ≤ (q.totient : ℝ)⁻¹ * ((if cand i j = true ∧ decD i j = false then SieveDrop.S2 (xq q) i j else 0) + C) +
        (q.totient : ℝ)⁻¹ * (if cand i j = true ∧ decD i j = true then dT3 (xq q) i j else 0) := add_le_add hA hB
    _ = _ := by ring

/-! ### The dropped sums against the costs -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [DeepGrid] in
/-- **A level of the sums**: if each tested term is at most `κ·F·w_c + e`, the tested sum is at most
`κ·F·Σ w + |s|·e`. -/
theorem sum_level {s : Finset ℕ} {P : ℕ → Prop} [DecidablePred P] {a : ℕ → ℝ} {w : ℕ → ℕ} {F : ℕ} {κ e : ℝ}
    (he : 0 ≤ e) (h : ∀ c ∈ s, P c → a c ≤ κ * ((F * w c : ℕ) : ℝ) + e) :
    ∑ c ∈ s, (if P c then a c else 0) ≤ κ * ((F * ∑ c ∈ s, (if P c then w c else 0) : ℕ) : ℝ) + s.card * e := by
  have h1 : ∀ c ∈ s, (if P c then a c else 0) ≤ κ * ((F * (if P c then w c else 0) : ℕ) : ℝ) + e := by
    intro c hc
    split_ifs with hp
    · exact h c hc hp
    · simp [he]
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Finset.mul_sum, Nat.cast_sum]

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [DeepGrid] in
theorem card_mul_le {N : ℕ} {M e : ℝ} (hN : (N : ℝ) ≤ M) (he : 0 ≤ e) : (N : ℝ) * e ≤ M * e :=
  mul_le_mul_of_nonneg_right hN he

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **The dropped sums of a cell `(i, j)` against its cost**, given the shares of its dropped cells at `x` with
`δ' ≥ 0` and `X ≥ 0`: `dT ≤ (costD/K)X + δ'·M·X`, `M = 1 + n²(1 + nC²(nC² + 1))`. -/
theorem dT_le_cost [SieveCert.GridOKC] {x δ' X : ℝ} (hδ' : 0 ≤ δ') (hX : 0 ≤ X) {i j : ℕ}
    (h2 : cand i j = true → SieveDrop.S2 x i j ≤ ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * X)
    (h4 : ∀ k < SieveCert.n, ∀ l < k + 1, counted4 i j k l = true →
      SB x (a4 i j k l) w4 ≤ (((P3 i j k * (Q4 (i + j + k) l * SC ^ 4) : ℕ) : ℝ) / (SC ^ 8 * K) + δ') * X)
    (h6 : ∀ k < SieveCert.n, ∀ l < k + 1, ∀ b < nC, ∀ c < b + 1, counted6 i j k l b c = true →
      SB x (a6 i j k l b c) w6 ≤ (((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC *
        (q6 (i + j + k + l + 4 * b) c * SC * SC) : ℕ) : ℝ) / (SC ^ 8 * K) + δ') * X)
    (h8 : ∀ k < SieveCert.n, ∀ l < k + 1, ∀ b < nC, ∀ c < b + 1, ∀ d < c + 1, ∀ f < d + 1,
      SieveBuch.reg8 i j k l b c d f = true →
      SB x (a8 i j k l b c d f) w8 ≤ (((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC *
        trapF (eC d) HC * (lastF (eC f) HC * omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f)
          (4 * H + 4 * HC) HC) : ℕ) : ℝ) / (SC ^ 8 * K) + δ') * X) :
    dT x i j ≤ (costD i j : ℝ) / K * X +
      δ' * (1 + (SieveCert.n : ℝ) * SieveCert.n * (1 + (nC : ℝ) * nC * (nC * nC + 1))) * X := by
  have hK := SieveCert.K_pos'
  have hS : (0 : ℝ) < SC ^ 8 := by have := SC_pos; positivity
  obtain ⟨κ, hκd⟩ : ∃ κ : ℝ, κ = X / (SC ^ 8 * K) := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by rw [hκd]; positivity
  obtain ⟨e0, he0⟩ : ∃ e0 : ℝ, e0 = δ' * X := ⟨_, rfl⟩
  have he0' : 0 ≤ e0 := by rw [he0]; exact mul_nonneg hδ' hX
  have conv : ∀ N : ℕ, ((N : ℝ) / (SC ^ 8 * K) + δ') * X = κ * N + e0 := fun N => by rw [hκd, he0]; ring
  have hn2 : 0 ≤ (nC : ℝ) * nC * e0 := by positivity
  have hn4 : 0 ≤ (nC : ℝ) * (nC * (nC * nC + 1)) * e0 := by positivity
  -- level 8
  have L8 : ∀ k < SieveCert.n, ∀ l < k + 1, ∀ b < nC, ∀ c < b + 1, ∀ d < c + 1,
      dT8 x i j k l b c d ≤ κ * ((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC *
        trapF (eC d) HC * Ch8 i j k l b c d : ℕ) : ℝ) + nC * e0 := by
    intro k hk l hl b hb c hc d hd
    have h := sum_level (s := range (d + 1)) (P := fun f => SieveBuch.reg8 i j k l b c d f = true)
      (a := fun f => SB x (a8 i j k l b c d f) w8)
      (w := fun f => lastF (eC f) HC * omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f)
        (4 * H + 4 * HC) HC)
      (F := P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC * trapF (eC d) HC) (κ := κ)
      (e := e0) he0'
      (fun f hf hr => (h8 k hk l hl b hb c hc d hd f (Finset.mem_range.1 hf) hr).trans (le_of_eq (conv _)))
    rw [Finset.card_range] at h
    refine h.trans (add_le_add le_rfl (card_mul_le ?_ he0'))
    exact_mod_cast (show d + 1 ≤ nC by omega)
  -- level 7
  have L7 : ∀ k < SieveCert.n, ∀ l < k + 1, ∀ b < nC, ∀ c < b + 1,
      dT7 x i j k l b c ≤ κ * ((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC *
        Ch7 i j k l b c : ℕ) : ℝ) + nC * (nC * e0) := by
    intro k hk l hl b hb c hc
    have h := sum_level (s := range (c + 1)) (P := fun d => SieveBuch.inKK7 i j k l b c d = true)
      (a := fun d => dT8 x i j k l b c d) (w := fun d => trapF (eC d) HC * Ch8 i j k l b c d)
      (F := P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC) (κ := κ) (e := nC * e0)
      (by positivity)
      (fun d hd _ => (L8 k hk l hl b hb c hc d (Finset.mem_range.1 hd)).trans (le_of_eq (by rw [Nat.mul_assoc])))
    rw [Finset.card_range] at h
    refine h.trans (add_le_add le_rfl (card_mul_le ?_ (by positivity)))
    exact_mod_cast (show c + 1 ≤ nC by omega)
  -- level 6
  have L6 : ∀ k < SieveCert.n, ∀ l < k + 1, ∀ b < nC,
      dT6 x i j k l b ≤ κ * ((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * Ch6 i j k l b : ℕ) : ℝ) +
        nC * ((nC * nC + 1) * e0) := by
    intro k hk l hl b hb
    have h := sum_level (s := range (b + 1)) (P := fun c => counted6 i j k l b c = true)
      (a := fun c => if dec6D i j k l b c = true then dT7 x i j k l b c else SB x (a6 i j k l b c) w6)
      (w := fun c => if dec6D i j k l b c = true then trapF (eC c) HC * Ch7 i j k l b c
        else q6 (i + j + k + l + 4 * b) c * SC * SC)
      (F := P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC) (κ := κ) (e := (nC * nC + 1) * e0)
      (by positivity) (fun c hc hcount => by
        have hc' := Finset.mem_range.1 hc
        split_ifs
        · refine (L7 k hk l hl b hb c hc').trans (add_le_add (le_of_eq (by rw [Nat.mul_assoc])) ?_)
          linarith
        · refine (h6 k hk l hl b hb c hc' hcount).trans ((le_of_eq (conv _)).trans (add_le_add le_rfl ?_))
          linarith)
    rw [Finset.card_range] at h
    refine h.trans (add_le_add le_rfl (card_mul_le ?_ (by positivity)))
    exact_mod_cast (show b + 1 ≤ nC by omega)
  -- level 5
  have L5 : ∀ k < SieveCert.n, ∀ l < k + 1,
      dT5 x i j k l ≤ κ * ((P3 i j k * trapF (SieveCert.e l) H * Ch5 i j k l : ℕ) : ℝ) +
        nC * (nC * ((nC * nC + 1) * e0)) := by
    intro k hk l hl
    have h := sum_level (s := range nC) (P := fun b => inKK5 i j k l b = true ∧ ne5 i j k l b = true)
      (a := fun b => dT6 x i j k l b) (w := fun b => trapF (eC b) HC * Ch6 i j k l b)
      (F := P3 i j k * trapF (SieveCert.e l) H) (κ := κ) (e := nC * ((nC * nC + 1) * e0)) (by positivity)
      (fun b hb _ => (L6 k hk l hl b (Finset.mem_range.1 hb)).trans (le_of_eq (by rw [Nat.mul_assoc])))
    rw [Finset.card_range] at h
    exact h
  -- level 4
  have L4 : ∀ k < SieveCert.n,
      dT4 x i j k ≤ κ * ((P3 i j k * Ch4 i j k : ℕ) : ℝ) +
        SieveCert.n * ((nC * (nC * (nC * nC + 1)) + 1) * e0) := by
    intro k hk
    have h := sum_level (s := range (k + 1)) (P := fun l => counted4 i j k l = true)
      (a := fun l => if dec4D i j k l = true then dT5 x i j k l else SB x (a4 i j k l) w4)
      (w := fun l => if dec4D i j k l = true then trapF (SieveCert.e l) H * Ch5 i j k l
        else Q4 (i + j + k) l * SC ^ 4)
      (F := P3 i j k) (κ := κ) (e := (nC * (nC * (nC * nC + 1)) + 1) * e0) (by positivity)
      (fun l hl hcount => by
        have hl' := Finset.mem_range.1 hl
        split_ifs
        · refine (L5 k hk l hl').trans (add_le_add (le_of_eq (by rw [Nat.mul_assoc])) ?_)
          linarith
        · refine (h4 k hk l hl' hcount).trans ((le_of_eq (conv _)).trans (add_le_add le_rfl ?_))
          linarith)
    rw [Finset.card_range] at h
    refine h.trans (add_le_add le_rfl (card_mul_le ?_ (by positivity)))
    exact_mod_cast (show k + 1 ≤ SieveCert.n by omega)
  -- level 3
  have L3 : dT3 x i j ≤ κ * ((1 * Ch3 i j : ℕ) : ℝ) +
      SieveCert.n * (SieveCert.n * ((nC * (nC * (nC * nC + 1)) + 1) * e0)) := by
    have h := sum_level (s := range SieveCert.n) (P := fun k => inKK i j k = true ∧ ne3 i j k = true)
      (a := fun k => dT4 x i j k) (w := fun k => P3 i j k * Ch4 i j k) (F := 1) (κ := κ)
      (e := SieveCert.n * ((nC * (nC * (nC * nC + 1)) + 1) * e0)) (by positivity)
      (fun k hk _ => (L4 k (Finset.mem_range.1 hk)).trans (le_of_eq (by rw [Nat.one_mul])))
    rw [Finset.card_range] at h
    exact h
  -- the cell
  have hM : 0 ≤ (SieveCert.n : ℝ) * (SieveCert.n * ((nC * (nC * (nC * nC + 1)) + 1) * e0)) := by positivity
  have hE : δ' * (1 + (SieveCert.n : ℝ) * SieveCert.n * (1 + (nC : ℝ) * nC * (nC * nC + 1))) * X =
      e0 + SieveCert.n * (SieveCert.n * ((nC * (nC * (nC * nC + 1)) + 1) * e0)) := by rw [he0]; ring
  unfold dT
  by_cases hc : cand i j = true
  · by_cases hd : decD i j = true
    · rw [ite_eq_right (show ¬(cand i j = true ∧ decD i j = false) by simp [hd]), zero_add,
        ite_eq_left ⟨hc, hd⟩]
      have hcost : costD i j = refcost i j := by simp [costD, hc, hd]
      rw [hcost]
      have h3 : (Ch3 i j : ℝ) ≤ SC ^ 8 * refcost i j := by
        exact_mod_cast Ch3_le (i := i) (j := j) DeepGrid.hHC DeepGrid.hH
      have h3' : κ * ((1 * Ch3 i j : ℕ) : ℝ) ≤ (refcost i j : ℝ) / K * X := by
        rw [Nat.one_mul]
        calc κ * (Ch3 i j : ℝ) ≤ κ * (SC ^ 8 * refcost i j) := mul_le_mul_of_nonneg_left h3 hκ
          _ = (SC : ℝ) ^ 8 * (X * refcost i j) / ((SC : ℝ) ^ 8 * K) := by rw [hκd]; ring
          _ = X * refcost i j / K := mul_div_mul_left _ _ hS.ne'
          _ = (refcost i j : ℝ) / K * X := by ring
      linarith
    · have hd' : decD i j = false := by simpa using hd
      rw [ite_eq_left ⟨hc, hd'⟩, ite_eq_right (show ¬(cand i j = true ∧ decD i j = true) from fun h => hd h.2),
        add_zero]
      have hcost : costD i j = bound2 (SieveCert.e i) (SieveCert.e j) := by simp [costD, hc, hd']
      rw [hcost]
      have h2' := h2 hc
      have : ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * X =
          (bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K * X + e0 := by rw [he0]; ring
      linarith
  · have hc' : cand i j = false := by simpa using hc
    rw [ite_eq_right (show ¬(cand i j = true ∧ decD i j = false) from fun h => hc h.1),
      ite_eq_right (show ¬(cand i j = true ∧ decD i j = true) from fun h => hc h.1), add_zero]
    have hcost : costD i j = 0 := by simp [costD, hc']
    rw [hcost, Nat.cast_zero, zero_div, zero_mul, zero_add]
    linarith

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] [DeepGrid] in
/-- The certificate's total in the reals: if `totalD/K ≤ c` (`htot`), then for `X ≥ 0`, `Σ_{i,j} (costD/K)X ≤ cX`. -/
theorem sum_costD_div {c : ℝ} (htot : (totalD : ℝ) / K ≤ c) (X : ℝ) (hX : 0 ≤ X) :
    ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (costD i j : ℝ) / K * X ≤ c * X := by
  have hsum : ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (costD i j : ℝ) / K * X =
      (totalD : ℝ) / K * X := by
    rw [totalD, SieveCert.sumTo_eq]
    simp only [SieveCert.sumTo_eq]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
  rw [hsum]
  exact mul_le_mul_of_nonneg_right htot hX

omit [Route] [RouteOK] [Fits] [SieveCert.IBPar] in
/-- **The shares, eventually**: for `δ' > 0` and large `x`, simultaneously, every candidate cell's `S2` and every
dropped box's sum (a counted cell of depth 4 or 6, a cell of depth 8 of a region) are at most their charges'
shares plus `δ'`, times `x/log x`. -/
theorem shares_ev8 [SieveCert.GridOKC] {δ' : ℝ} (hδ' : 0 < δ') : ∀ᶠ x : ℝ in atTop,
    ∀ i ∈ range SieveCert.n, ∀ j ∈ range SieveCert.n,
    (cand i j = true →
      SieveDrop.S2 x i j ≤ ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * (x / Real.log x)) ∧
    ∀ k ∈ range SieveCert.n, ∀ l ∈ range SieveCert.n,
    (counted4 i j k l = true →
      SB x (a4 i j k l) w4 ≤ (((P3 i j k * (Q4 (i + j + k) l * SC ^ 4) : ℕ) : ℝ) / (SC ^ 8 * K) + δ') *
        (x / Real.log x)) ∧
    ∀ b ∈ range nC, ∀ c ∈ range nC,
    (counted6 i j k l b c = true →
      SB x (a6 i j k l b c) w6 ≤ (((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC *
        (q6 (i + j + k + l + 4 * b) c * SC * SC) : ℕ) : ℝ) / (SC ^ 8 * K) + δ') * (x / Real.log x)) ∧
    ∀ d ∈ range nC, ∀ f ∈ range nC, SieveBuch.reg8 i j k l b c d f = true →
      SB x (a8 i j k l b c d f) w8 ≤ (((P3 i j k * trapF (SieveCert.e l) H * trapF (eC b) HC * trapF (eC c) HC *
        trapF (eC d) HC * (lastF (eC f) HC * omKw (7 * V + H * (i + j + k + l + 4 * b + 4 * c + 4 * d)) (eC f)
          (4 * H + 4 * HC) HC) : ℕ) : ℝ) / (SC ^ 8 * K) + δ') * (x / Real.log x) := by
  rw [Filter.eventually_all_finset]
  intro i _
  rw [Filter.eventually_all_finset]
  intro j _
  refine Filter.Eventually.and ?_ ?_
  · by_cases hc : cand i j = true
    · filter_upwards [share2_of_cand hc hδ'] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hc
  rw [Filter.eventually_all_finset]
  intro k _
  rw [Filter.eventually_all_finset]
  intro l _
  refine Filter.Eventually.and ?_ ?_
  · by_cases hc : counted4 i j k l = true
    · filter_upwards [share4D hc hδ'] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hc
  rw [Filter.eventually_all_finset]
  intro b _
  rw [Filter.eventually_all_finset]
  intro c _
  refine Filter.Eventually.and ?_ ?_
  · by_cases hc : counted6 i j k l b c = true
    · filter_upwards [share6D DeepGrid.hHC hc hδ'] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hc
  rw [Filter.eventually_all_finset]
  intro d _
  rw [Filter.eventually_all_finset]
  intro f _
  by_cases hc : SieveBuch.reg8 i j k l b c d f = true
  · filter_upwards [share8D DeepGrid.hHC DeepGrid.fit8 hc hδ'] with x hx _
    exact hx
  · exact Filter.Eventually.of_forall fun x h => absurd h hc

/-- **The dropped terms, for large `q`, with the loss as a parameter**: for a route with `RouteOK` and grids with
`GridOK`, `GridOKC` and `DeepGrid` that fit (`Fits`), if `totalD/K ≤ c` in the reals (`htot`), then for `ε > 0`,
`E1(g_B) ≤ φ(q)⁻¹(c + ε)x/log x`. -/
theorem drop_ev8 [SieveCert.GridOKC] {c : ℝ} (htot : (totalD : ℝ) / K ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, LargeQ q →
    (parQ q).E1 (gB q) ≤ (q.totient : ℝ)⁻¹ * ((c + ε) * (xq q / Real.log (xq q))) := by
  have hn : (0 : ℝ) < SieveCert.n := by exact_mod_cast SieveCert.n_pos
  set Mc : ℝ := 1 + (SieveCert.n : ℝ) * SieveCert.n * (1 + (nC : ℝ) * nC * (nC * nC + 1)) with hMc
  have hMc0 : 0 < Mc := by positivity
  set M : ℝ := (SieveCert.n : ℝ) * SieveCert.n * Mc with hM
  have hM0 : 0 < M := by positivity
  set δ' : ℝ := ε / (2 * M) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  filter_upwards [SieveDrop.tendsto_xq.eventually (shares_ev8 hδ'0), SieveDrop.corner_ev (half_pos hε),
    eventually_ge_atTop 1] with q hS hC hq1 hL
  have G := good_of_large hL
  set X := xq q / Real.log (xq q) with hX
  have hx1 : 1 < xq q := G.hx
  have hX0 : 0 ≤ X := div_nonneg (by linarith) (Real.log_nonneg hx1.le)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hdrop : ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dT (xq q) i j ≤ c * X + ε / 2 * X := by
    calc ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dT (xq q) i j
        ≤ ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, ((costD i j : ℝ) / K * X + δ' * Mc * X) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          obtain ⟨h2, h468⟩ := hS i hi j hj
          have mem : ∀ {a m : ℕ}, a < m → a ∈ range m := fun h => Finset.mem_range.2 h
          exact dT_le_cost hδ'0.le hX0 h2
            (fun k hk l hl hc => (h468 k (mem hk) l (mem (by omega))).1 hc)
            (fun k hk l hl b hb c hc' hc => ((h468 k (mem hk) l (mem (by omega))).2 b (mem hb) c
              (mem (by omega))).1 hc)
            (fun k hk l hl b hb c hc' d hd f hf hr => ((h468 k (mem hk) l (mem (by omega))).2 b (mem hb) c
              (mem (by omega))).2 d (mem (by omega)) f (mem (by omega)) hr)
      _ = ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (costD i j : ℝ) / K * X +
            SieveCert.n * SieveCert.n * (δ' * Mc * X) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ c * X + ε / 2 * X := by
          have h1 := sum_costD_div htot X hX0
          have h2 : (SieveCert.n : ℝ) * SieveCert.n * (δ' * Mc * X) = ε / 2 * X := by
            rw [hδ']
            field_simp
            rw [hM]
            ring
          linarith
  calc (parQ q).E1 (gB q)
      ≤ (q.totient : ℝ)⁻¹ * (∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dT (xq q) i j +
          (SieveCert.n : ℝ) ^ 2 * ((SieveDrop.cornerP (parQ q).ztop).card : ℝ) ^ 2) := E1_le G hC.1 hq1
    _ ≤ (q.totient : ℝ)⁻¹ * ((c * X + ε / 2 * X) + ε / 2 * X) :=
        mul_le_mul_of_nonneg_left (add_le_add hdrop hC.2) hφ
    _ = (q.totient : ℝ)⁻¹ * ((c + ε) * X) := by ring

end Drops

end SieveDrop8
