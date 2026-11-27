import GainExponents

/-!
# The Stage-2 clause G2 and the narrow window of the top shifts: statements

A step of the proof of the sharp frontier (`SharpInputs`, the design's Stage 2): the statements of the two Stage-2
clauses that read the local theory's data at a prime, so that the local theory and the assembly (M-G8) can be stated
against them, and the box selection that will give them. They are not clauses of `SharpDesign.Adm`: G2 reads the
local theory's per-orbit `κ` (`κG p t₀ aZ bT`, fixed by the glue to the first local theorem), which is not upstream of
`SharpAdm`, and it shares the parameters `pr` with `SharpDesign.FamAt`; M-G8 adds both to a downstream clause
(`Adm ∧ ∃ pr, FamAt pr ∧ BTNarrow pr ∧ G2At κG pr`).

* **The narrow window** (`SharpDesign.BTNarrow`): every top shift `b_t` lies in `W_b` (`scWb`), which sits inside the
  window `[b′, b′(1 + x^{−1/4})]` of `FamAt.bT_mem`.
* **G2** (`SharpDesign.G2At`): the mean exceptional fraction at the candidates `p ≥ p₀` (`scP0`), weighted by
  `log p/p` and summed over the served orbits (`SharpDesign.served`), is at most `x^{−9−ε}/6`.
* **The box selection** (`exists_le_boxMean`): a real function on the box `W_a^{TT} × W_b^{TT}` (the values off `TT`
  fixed) is at most its mean at some point of the box (a minimiser is at most the mean).
-/

open Finset

namespace ZetaBalance

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-- **(A7, Stage 2) The narrow window**: every top shift in `W_b`. -/
def SharpDesign.BTNarrow (Dg : SharpDesign S κ x ε X) (pr : DesignPar S) : Prop :=
  ∀ t ∈ Dg.TT, pr.bT t ∈ scWb S x ε Dg.R.k

/-- **(G2)** Small mean exceptional fraction at the candidates `p ≥ p₀`, for the local theory's per-orbit
`κ_p(t₀)` (`κG p t₀ aZ bT`, fixed by the glue to the first local theorem). -/
def SharpDesign.G2At (Dg : SharpDesign S κ x ε X) (κG : ℕ → S.A → (S.A → ℤ) → (S.A → ℤ) → ℝ)
    (pr : DesignPar S) : Prop :=
  ∑ p ∈ (S.cand κ x ε Dg.R.k).filter (fun p : ℕ => scP0 x Dg.R.k ≤ p),
    (Real.log p / p) * ∑ t₀ ∈ Dg.served p, κG p t₀ pr.aZ pr.bT ≤ x ^ (-9 - ε) / 6

/-- **The box selection** (G2's existence): a real function on the box `W_a^{TT} × W_b^{TT}` (values off `TT`
fixed) is at most its mean somewhere in the box: a minimiser `m` over the box has `F(m)·|box| ≤ Σ_box F`. -/
theorem exists_le_boxMean (TT : Finset S.A) (Wa Wb : Finset ℤ) (za zb : ℤ) (hWa : Wa.Nonempty)
    (hWb : Wb.Nonempty) (F : (S.A → ℤ) → (S.A → ℤ) → ℝ) :
    ∃ aZ ∈ Fintype.piFinset (fun t => if t ∈ TT then Wa else {za}),
      ∃ bT ∈ Fintype.piFinset (fun t => if t ∈ TT then Wb else {zb}),
        F aZ bT * (((Fintype.piFinset (fun t => if t ∈ TT then Wa else {za})).card : ℝ) *
          (Fintype.piFinset (fun t => if t ∈ TT then Wb else {zb})).card) ≤
        ∑ a ∈ Fintype.piFinset (fun t => if t ∈ TT then Wa else {za}),
          ∑ b ∈ Fintype.piFinset (fun t => if t ∈ TT then Wb else {zb}), F a b := by
  set BA := Fintype.piFinset (fun t => if t ∈ TT then Wa else {za})
  set BB := Fintype.piFinset (fun t => if t ∈ TT then Wb else {zb})
  have hA : BA.Nonempty := Fintype.piFinset_nonempty.2 fun t => by
    split_ifs
    · exact hWa
    · exact singleton_nonempty _
  have hB : BB.Nonempty := Fintype.piFinset_nonempty.2 fun t => by
    split_ifs
    · exact hWb
    · exact singleton_nonempty _
  obtain ⟨m, hm, hmin⟩ := exists_min_image (BA ×ˢ BB) (fun ab => F ab.1 ab.2) (hA.product hB)
  obtain ⟨hmA, hmB⟩ := mem_product.1 hm
  refine ⟨m.1, hmA, m.2, hmB, ?_⟩
  calc F m.1 m.2 * ((BA.card : ℝ) * BB.card) = ∑ _a ∈ BA, ∑ _b ∈ BB, F m.1 m.2 := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ ∑ a ∈ BA, ∑ b ∈ BB, F a b :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => hmin (a, b) (mem_product.2 ⟨ha, hb⟩)

end ZetaBalance
