/-
# `PYWeyl` contains `WeylBound`: the Weyl bound for every character gives the Weyl bound for ζ

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`weylBound_of_PYWeyl`). `LinnikWeyl.PYWeyl`, the hypothesis that `‖L(1/2 + it, χ)‖ ≤ C (q(1 + |t|))^{1/6+ε}`
for every modulus `q ≥ 1`, every `χ` mod `q` and every real `t`, implies `CrossCriteria.WeylBound`, the hypothesis that
`‖ζ(1/2 + it)‖ ≤ C |t|^{1/6+ε}` for `|t| ≥ 2` (`lib/core/CrossCriteria.lean`).

It is the case `q = 1` of `PYWeyl`: the only character mod `1` is the trivial one, whose `L`-function is `ζ`
(`DirichletCharacter.LFunction_modOne_eq`), and `1 + |t| ≤ 2|t|` for `|t| ≥ 1`, so the constant becomes `C · 2^{1/6+ε}`.
Both are hypotheses, not theorems: this module proves the implication, not either hypothesis, and the converse does not
hold (`WeylBound` is a statement about ζ alone). It joins the Linnik layer's `PYWeyl` (`LinnikWeyl`) to the core layer's
`CrossCriteria` list of the exact missing Props (`ConvexityBound`, `WeylBound`, `Lindelof`, `DensityHypothesis`).

* `weylBound_of_PYWeyl`: `PYWeyl → WeylBound`.
-/
import LinnikWeyl
import CrossCriteria

open Complex DirichletCharacter

namespace LinnikWeylBridge

/-- `LinnikWeyl.PYWeyl` (all moduli, jointly in `q` and `t`) gives `CrossCriteria.WeylBound` (ζ alone), by its case
`q = 1`. -/
theorem weylBound_of_PYWeyl (h : LinnikWeyl.PYWeyl) : CrossCriteria.WeylBound := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := h ε hε
  refine ⟨C * 2 ^ (1 / 6 + ε), fun t ht => ?_⟩
  have h1 := hC 1 (1 : DirichletCharacter ℂ 1) t
  rw [DirichletCharacter.LFunction_modOne_eq] at h1
  have e : ((1 : ℕ) : ℝ) * (1 + |t|) = 1 + |t| := by simp
  rw [e] at h1
  refine h1.trans ?_
  have ht1 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hle : (1 + |t|) ^ (1 / 6 + ε) ≤ (2 * |t|) ^ (1 / 6 + ε) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
  rw [Real.mul_rpow (by norm_num) ht1] at hle
  calc C * (1 + |t|) ^ (1 / 6 + ε) ≤ C * (2 ^ (1 / 6 + ε) * |t| ^ (1 / 6 + ε)) :=
        mul_le_mul_of_nonneg_left hle hC0
    _ = C * 2 ^ (1 / 6 + ε) * |t| ^ (1 / 6 + ε) := by ring

end LinnikWeylBridge

#print axioms LinnikWeylBridge.weylBound_of_PYWeyl
