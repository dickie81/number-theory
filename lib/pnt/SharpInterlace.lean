import SharpAdm

/-!
# The design's weights interlace

A step of the construction's period data (`SharpCons`, the field `P`): the branching weight `σ = sgT(k, t, m; v, b, e)`
of the translate's Harish-Chandra family `hc u` interlaces the column weight `λ_m = wt(k, t, m; ⌊u − ½⌋, e)` of any
word family pinned to `u` (`SharpDesign.PinnedTo`): `λ_{i+1} ≤ σ_i ≤ λ_i` at every place and every `i < N_m − 1`. So
the branching constant is nonzero (`PeriodTarget.brConst_ne_zero`) and the Fock projection onto `VV(σ)` exists
(`PeriodTarget.exists_isFockProj` with `PeriodTarget.antitone_of_interlace_right`).

**Route.** Only the Harish-Chandra inequalities are used (`Setting.Ranks.HC`), not admissibility. With `k = 2c`,
`t = 2g + 1`, `h = (t + 1)/2 = g + 1` and `(N_m − 2)/2 = c − 1 + mh`, the entries are read off the definitions
(`wt_of_lt`, `wt_of_eq`, `sgHC_of_eq`):
* on `i < k − 1`, `σ_i = v_i + i + 1 − c − mh`, between `λ_{i+1} = ⌊u_{i+1} − ½⌋ + i + 2 − c − mh` and
  `λ_i = ⌊u_i − ½⌋ + i + 1 − c − mh`, as `u_{i+1} < v_i < u_i` with `u ∈ ℤ + ½` (`floor_add_one_le`,
  `le_floor_sub_half`);
* at `i = k − 1 + q(t + 1)`, `σ_i = −b_q + c + 2qh − mh`, above `λ_{i+1} = −e_q + c + (2q + 1)h − mh` as
  `e_q − b_q ≥ h + 1`, and below `λ_i`, which is `⌊u_{k−1} − ½⌋ + c − mh` for `q = 0` (`−b_0 < u_{k−1}`) and
  `−e_{q−1} + c + (2q − 1)h − mh` else (`b_q − e_{q−1} ≥ h + 1`);
* at `i = k − 1 + q(t + 1) + r`, `1 ≤ r ≤ t`, all three are `−e_q + c + (2q + 1)h − mh`.
-/

namespace ZetaBalance

/-! ## The branching weight interlaces the column weight -/

section Interlace

/-- **The column weight on the first `k` entries**: `λ_i = u_i + 1 + i − k/2 − jh` (`WeylFock.wt`, `i < k`). -/
theorem wt_of_lt {Φ' : Type*} {k t j : ℕ} (u : Φ' → Fin k → ℤ) (e : Φ' → ℕ → ℤ) (ρ : Φ')
    (i : Fin (k + j * (t + 1))) (hi : (i : ℕ) < k) :
    WeylFock.wt k t j u e ρ i = u ρ ⟨i, hi⟩ + 1 + (i : ℕ) - (k / 2 : ℕ) - j * ((t + 1) / 2 : ℕ) := by
  simp [WeylFock.wt, hi]

/-- **The column weight on block `B`**: `λ_i = −e_B + k/2 + (2B + 1)h − jh` at `i = k + B(t + 1) + r`, `r ≤ t`
(`WeylFock.wt`). -/
theorem wt_of_eq {Φ' : Type*} {k t j : ℕ} (u : Φ' → Fin k → ℤ) (e : Φ' → ℕ → ℤ) (ρ : Φ')
    (i : Fin (k + j * (t + 1))) {B r : ℕ} (hr : r ≤ t) (hi : (i : ℕ) = k + B * (t + 1) + r) :
    WeylFock.wt k t j u e ρ i = -e ρ B + (k / 2 : ℕ) + (2 * B + 1) * ((t + 1) / 2 : ℕ) - j * ((t + 1) / 2 : ℕ) := by
  have hN : ((i : ℕ) - k) / (t + 1) = B := by
    rw [hi, show k + B * (t + 1) + r - k = r + B * (t + 1) by omega, Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  have hZ : (((i : ℕ) : ℤ) - k) / ((t : ℤ) + 1) = B := by
    rw [show ((i : ℕ) : ℤ) - k = (((i : ℕ) - k : ℕ) : ℤ) by omega,
      show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by push_cast; ring, ← Int.natCast_div, hN]
  simp only [WeylFock.wt, show ¬(i : ℕ) < k by omega, ↓reduceDIte, hN, hZ]

/-- **`⌊u − ½⌋ + 1 ≤ v`** for a half-integer `u < v`, `v ∈ ℤ`. -/
theorem floor_add_one_le {u : ℚ} {v : ℤ} (hu : ∃ z : ℤ, u = z + 1 / 2) (h : u < v) : ⌊u - 1 / 2⌋ + 1 ≤ v := by
  obtain ⟨z, rfl⟩ := hu
  rw [show (z : ℚ) + 1 / 2 - 1 / 2 = z by ring, Int.floor_intCast]
  have : (z : ℚ) < v := by linarith
  exact_mod_cast this

/-- **`v ≤ ⌊u − ½⌋`** for a half-integer `u > v`, `v ∈ ℤ`. -/
theorem le_floor_sub_half {u : ℚ} {v : ℤ} (hu : ∃ z : ℤ, u = z + 1 / 2) (h : (v : ℚ) < u) : v ≤ ⌊u - 1 / 2⌋ := by
  obtain ⟨z, rfl⟩ := hu
  rw [show (z : ℚ) + 1 / 2 - 1 / 2 = z by ring, Int.floor_intCast]
  have : (v : ℚ) < z + 1 := by linarith
  exact Int.lt_add_one_iff.1 (by exact_mod_cast this)

/-- **The branching weight on block `q`** (`PeriodTarget.sgHC`): at `i = k − 1 + q(t + 1) + r`, `r ≤ t`, it is
`−b_q` for `r = 0` and `−e_q + h − r` else. -/
theorem sgHC_of_eq {Φ' : Type*} {n k t : ℕ} (v b e : Φ' → ℕ → ℤ) (ρ : Φ') (i : Fin n) {q r : ℕ} (hk : 1 ≤ k)
    (hr : r ≤ t) (hi : (i : ℕ) + 1 = k + q * (t + 1) + r) :
    PeriodTarget.sgHC k t v b e ρ i = if r = 0 then -b ρ q else -e ρ q + ((t + 1) / 2 : ℕ) - r := by
  have hd : (i : ℕ) - (k - 1) = r + q * (t + 1) := by omega
  have hmod : ((i : ℕ) - (k - 1)) % (t + 1) = r := by
    rw [hd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hdiv : ((i : ℕ) - (k - 1)) / (t + 1) = q := by
    rw [hd, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  simp only [PeriodTarget.sgHC, show ¬(i : ℕ) < k - 1 by omega, ↓reduceIte, hmod, hdiv]

namespace Setting.Ranks

variable {S : Setting} (R : S.Ranks)

/-- **The branching weight interlaces the column weight** (C2g): for Harish-Chandra families `hw` (the word's) and
`hc` (the translate's) with the same `v`, `b`, `e`, at rank `n = N_m − 1`, the row weight
`σ = sgT(k, t, m; v, b, e)` of `hc` and the column weight `λ = wt(k, t, m; ⌊u − ½⌋, e)` of `hw` (`λ_m`, read at rank
`n + 1 = N_m`) have `λ_{i+1} ≤ σ_i ≤ λ_i` for every place `ρ` and `i < n`. With `h = (t + 1)/2`:
* on `i < k − 1`, `σ_i − λ_i = v_i − ⌊u_i − ½⌋` and `σ_i − λ_{i+1} = v_i − ⌊u_{i+1} − ½⌋ − 1` (`u_{i+1} < v_i < u_i`);
* at `i = k − 1 + q(t + 1)`, `σ_i = −b_q + k/2 + 2qh − mh`, against `λ_{i+1} = −e_q + k/2 + (2q + 1)h − mh` and
  `λ_i = ⌊u_{k−1} − ½⌋ + k/2 − mh` (`q = 0`) or `−e_{q−1} + k/2 + (2q − 1)h − mh` (`e_j − b_j ≥ h + 1`,
  `b_{j+1} − e_j ≥ h + 1`, `−b_0 < u_{k−1}`);
* at `i = k − 1 + q(t + 1) + r`, `1 ≤ r ≤ t`, `σ_i = λ_i = λ_{i+1} = −e_q + k/2 + (2q + 1)h − mh`. -/
theorem interlace (hw hc : R.HCFamily) (hp : ∀ ρ, (hw ρ).v = (hc ρ).v ∧ (hw ρ).b = (hc ρ).b ∧ (hw ρ).e = (hc ρ).e)
    {n : ℕ} (hn : n + 1 = R.k + R.m * (R.t + 1)) (ρ : Φ S.A) (i : Fin n) :
    WeylFock.wt R.k R.t R.m (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ (Fin.cast hn i.succ) ≤
        PeriodTarget.sgT R.k R.t R.m (fun ρ => finN (hc ρ).v) (fun ρ => finN (hc ρ).b) (fun ρ => finN (hc ρ).e) ρ
          i ∧
      PeriodTarget.sgT R.k R.t R.m (fun ρ => finN (hc ρ).v) (fun ρ => finN (hc ρ).b) (fun ρ => finN (hc ρ).e) ρ i ≤
        WeylFock.wt R.k R.t R.m (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
          (Fin.cast hn i.castSucc) := by
  obtain ⟨hv, hb, he⟩ := hp ρ
  have hm2 := R.two_le_m
  have hk3 := R.m_add_three_le
  obtain ⟨c, hc2⟩ := R.k_even
  obtain ⟨g, hg⟩ := R.t_odd
  have hT : (R.t + 1) / 2 = g + 1 := by omega
  have hK : R.k / 2 = c := by omega
  have hmt : R.m * (R.t + 1) = 2 * (R.m * (g + 1)) := by rw [hg]; ring
  have hN : (((n - 1) / 2 : ℕ) : ℤ) = c - 1 + R.m * (g + 1) := by
    rw [show (n - 1) / 2 = (c - 1) + R.m * (g + 1) by omega, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ c)]
    push_cast
    ring
  have he3 : ((R.t : ℤ) + 3) / 2 = g + 2 := by omega
  have hi := i.isLt
  simp only [PeriodTarget.sgT, PeriodTarget.sg, PeriodTarget.rhoW, hN]
  by_cases hA : (i : ℕ) < R.k - 1
  · -- the entries `v`
    rw [wt_of_lt _ _ _ _ (by simp; omega), wt_of_lt _ _ _ _ (by simp; omega)]
    simp only [PeriodTarget.sgHC, hA, ↓reduceIte, finN, ↓reduceDIte, ← hv, Fin.val_cast, Fin.val_succ,
      Fin.val_castSucc, hT, hK]
    have h1 := floor_add_one_le ((hw ρ).u_half _) ((hw ρ).lt_v ⟨i, hA⟩)
    have h2 := le_floor_sub_half ((hw ρ).u_half _) ((hw ρ).v_lt ⟨i, hA⟩)
    simp only [Fin.castLE_mk] at h2
    push_cast
    constructor <;> linarith
  · -- the blocks: `i = k − 1 + q(t + 1) + r`
    obtain ⟨q, r, hr, hiq⟩ : ∃ q r, r ≤ R.t ∧ (i : ℕ) + 1 = R.k + q * (R.t + 1) + r :=
      ⟨((i : ℕ) - (R.k - 1)) / (R.t + 1), ((i : ℕ) - (R.k - 1)) % (R.t + 1),
        Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega)), by have := Nat.div_add_mod' ((i : ℕ) - (R.k - 1)) (R.t + 1); omega⟩
    have hq : q < R.m := Nat.lt_of_mul_lt_mul_right (a := R.t + 1) (by omega)
    have hqt : q * (R.t + 1) = 2 * (q * (g + 1)) := by rw [hg]; ring
    have hiz : ((i : ℕ) : ℤ) = 2 * c + 2 * (q * (g + 1)) + r - 1 := by
      have h' := congrArg (Nat.cast : ℕ → ℤ) (show (i : ℕ) + 1 = 2 * c + 2 * (q * (g + 1)) + r by omega)
      push_cast at h'
      linarith
    have heb := (hw ρ).e_sub_b ⟨q, hq⟩
    rw [sgHC_of_eq _ _ _ _ _ (by omega) hr hiq, wt_of_eq _ _ _ _ hr (by simpa using hiq)]
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · rcases q with _ | q'
      · -- `i = k − 1`: `−b_0 ≤ ⌊u_{k−1} − ½⌋`
        rw [wt_of_lt _ _ _ _ (by simp; omega)]
        simp only [ite_true, finN, hq, ↓reduceDIte, ← hb, ← he, Fin.val_cast, Fin.val_castSucc, hT, hK]
        have h1 := le_floor_sub_half (v := -(hw ρ).b ⟨0, by omega⟩) ((hw ρ).u_half _)
          (by push_cast; exact (hw ρ).neg_b_lt)
        rw [show (⟨(i : ℕ), by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ from Fin.ext (by simp; omega)]
        push_cast at hiz ⊢
        constructor <;> linarith
      · -- `i = k − 1 + (q' + 1)(t + 1)`: `e_{q'} + h ≤ b_{q'+1}`
        rw [wt_of_eq _ _ _ _ (B := q') (r := R.t) le_rfl (by simp; rw [add_one_mul] at hiq; omega)]
        simp only [ite_true, finN, hq, show q' < R.m by omega, ↓reduceDIte, ← hb, ← he, hT, hK]
        have hbe := (hw ρ).b_sub_e ⟨q', by omega⟩ hq
        push_cast at hiz ⊢
        constructor <;> linarith
    · -- `1 ≤ r ≤ t`: `σ_i = λ_i = λ_{i+1}`
      rw [wt_of_eq _ _ _ _ (B := q) (r := r - 1) (by omega) (by simp; omega)]
      simp only [show r ≠ 0 by omega, ite_false, finN, hq, ↓reduceDIte, ← he, hT, hK]
      push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at hiz ⊢
      constructor <;> linarith

end Setting.Ranks

end Interlace

/-- **A pinned word family's `λ_m` interlaces the translate's `σ`** (`Setting.Ranks.interlace`): a family pinned to
`u` has the `v`, `b`, `e` of `hc u`. -/
theorem SharpDesign.PinnedTo.interlace {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}
    {Dg : SharpDesign S κ x ε X} {u : S.A} {hw : Dg.R.HCFamily}
    (hp : Dg.PinnedTo u hw) {n : ℕ} (hn : n + 1 = Dg.R.k + Dg.R.m * (Dg.R.t + 1)) (ρ : Φ S.A) (i : Fin n) :
    WeylFock.wt Dg.R.k Dg.R.t Dg.R.m (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
          (Fin.cast hn i.succ) ≤
        PeriodTarget.sgT Dg.R.k Dg.R.t Dg.R.m (fun ρ => finN (Dg.hc u ρ).v) (fun ρ => finN (Dg.hc u ρ).b)
          (fun ρ => finN (Dg.hc u ρ).e) ρ i ∧
      PeriodTarget.sgT Dg.R.k Dg.R.t Dg.R.m (fun ρ => finN (Dg.hc u ρ).v) (fun ρ => finN (Dg.hc u ρ).b)
          (fun ρ => finN (Dg.hc u ρ).e) ρ i ≤
        WeylFock.wt Dg.R.k Dg.R.t Dg.R.m (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
          (Fin.cast hn i.castSucc) :=
  Dg.R.interlace hw (Dg.hc u) (fun ρ => ⟨(hp ρ).1, (hp ρ).2.1, (hp ρ).2.2.1⟩) hn ρ i

end ZetaBalance
