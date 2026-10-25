/-
# Linnik's exponents `9/4` and `226/100` from the Chen–Gupta–Li chain

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

These are the final theorems that the chain `LinnikCGLMat`, `LinnikCGLS23`, `LinnikCGLS2`, `LinnikCGLS3`,
`LinnikCGLP81`, `LinnikCGLHB101`, `LinnikCGLDensity` draws from Chen–Gupta–Li's Proposition 3.1: at each module's
hypothesis (the bound on the cubic trace, the `S₂` and `S₃` hypotheses, `S₃` alone, Proposition 8.1 and Heath-Brown's
Theorem 10.1, Theorem 10.1 alone), with no hypothesis, and from `LinnikCGLDensity.cglDensity`. Each theorem keeps the
name and the namespace it had in that module (`LinnikCGLMat.linnik_225c_third`, …, `LinnikCGLHB101.linnik_225`,
`LinnikCGLDensity.linnik_225c`), and its proof.

They moved here because their proofs use `LinnikCGLLinnik` (and so the certificates of `Linnik225C` and
`Linnik226C`), which no module of the density chain itself, and neither `Linnik22322R` nor the since removed `Linnik22475R` (commit
`6df0ebd`), needs. The chain's modules no longer import them, so building `Linnik22322R` no longer builds the
`SieveCert225C` (167 parts) and `SieveCert226` (5 parts) certificates. `CheckAll.lean` imports this file.

Plain statements. Each is: there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ Kq^{9/4}`, or with `p ≤ Kq^{226/100}`, from the module's hypothesis:
* `LinnikCGLMat.linnik_225c_third`, `linnik_226c_third`: from `CGLThird`.
* `LinnikCGLS23.linnik_225c_s23`, `linnik_226c_s23`: from `CGLS2` and `CGLS3`.
* `LinnikCGLS2.linnik_225c_s3`, `linnik_226c_s3`: from `CGLS3`.
* `LinnikCGLS3.linnik_225c_pt`, `linnik_226c_pt`: from `CGLP81` and `CGLT101`.
* `LinnikCGLP81.linnik_225c_t101`, `linnik_226c_t101`: from `CGLT101`.
* `LinnikCGLHB101.linnik_225`, `linnik_226`: with no hypothesis.
* `LinnikCGLDensity.linnik_225c`, `linnik_226c`: `Linnik225C.linnik_225c` and `Linnik226C.linnik_226c` at
  `cglDensity`.

The file imports `LinnikCGLLinnik.lean` and `LinnikCGLDensity.lean`.
-/
import LinnikCGLLinnik
import LinnikCGLDensity

open Complex Real Finset

noncomputable section

namespace LinnikCGLMat

open DirichletCharacter LinnikMoment Matrix

/-- **Linnik's theorem with exponent `9/4` from the bound on the cubic trace** (`h`). -/
theorem linnik_225c_third (h : CGLThird) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLLinnik.linnik_225c_lv (prop31_of_third h)

/-- **Linnik's theorem with exponent `226/100` from the bound on the cubic trace** (`h`). -/
theorem linnik_226c_third (h : CGLThird) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLLinnik.linnik_226c_lv (prop31_of_third h)

end LinnikCGLMat

namespace LinnikCGLS23

open DirichletCharacter LinnikCGLMat

/-- **Linnik's theorem with exponent `9/4` from the `S₂` and `S₃` hypotheses.** -/
theorem linnik_225c_s23 (h2 : CGLS2) (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  linnik_225c_third (third_of_s23 h2 h3)

/-- **Linnik's theorem with exponent `226/100` from the `S₂` and `S₃` hypotheses.** -/
theorem linnik_226c_s23 (h2 : CGLS2) (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  linnik_226c_third (third_of_s23 h2 h3)

end LinnikCGLS23

namespace LinnikCGLS2

open LinnikCGLMat LinnikCGLS23 LinnikCGLMellin LinnikCGLReflect LinnikCGLPair LinnikCGLFrob DirichletCharacter
  LinnikReflect LinnikPower

/-- **Linnik's theorem with exponent `9/4` from the `S₃` hypothesis alone**: `linnik_225c_s23` with
`cgls2`. -/
theorem linnik_225c_s3 (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  linnik_225c_s23 cgls2 h3

/-- **Linnik's theorem with exponent `226/100` from the `S₃` hypothesis alone**: `linnik_226c_s23` with
`cgls2`. -/
theorem linnik_226c_s3 (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  linnik_226c_s23 cgls2 h3

end LinnikCGLS2

namespace LinnikCGLS3

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLS23 LinnikCGLDiag LinnikCGLTrunc LinnikCGLP71
  LinnikCGLP72 LinnikCGLRt LinnikCGLMom4 LinnikCGLJ LinnikCGL112 LinnikCGLT101 LinnikCGLCase LinnikCGLEps

/-- **Linnik's theorem with exponent `9/4` from their Proposition 8.1 and Heath-Brown's Theorem 10.1**:
`linnik_225c_s3` with `cgls3`. -/
theorem linnik_225c_pt (hP : CGLP81) (hT : CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLS2.linnik_225c_s3 (cgls3 hP hT)

/-- **Linnik's theorem with exponent `226/100` from their Proposition 8.1 and Heath-Brown's Theorem 10.1**:
`linnik_226c_s3` with `cgls3`. -/
theorem linnik_226c_pt (hP : CGLP81) (hT : CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLS2.linnik_226c_s3 (cgls3 hP hT)

end LinnikCGLS3

namespace LinnikCGLP81

open LinnikCGLRt LinnikCGLMom LinnikCGLJ LinnikCGLG LinnikCGLFtil LinnikCGLJtil LinnikCGLTail LinnikCGLConst
  LinnikCGLForm LinnikCGLFtilP LinnikCGLCov

/-- **Linnik's theorem with exponent `9/4` from Heath-Brown's Theorem 10.1 alone**: `linnik_225c_pt`
with `cglp81`. -/
theorem linnik_225c_t101 (hT : LinnikCGLT101.CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLS3.linnik_225c_pt cglp81 hT

/-- **Linnik's theorem with exponent `226/100` from Heath-Brown's Theorem 10.1 alone**:
`linnik_226c_pt` with `cglp81`. -/
theorem linnik_226c_t101 (hT : LinnikCGLT101.CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLS3.linnik_226c_pt cglp81 hT

end LinnikCGLP81

namespace LinnikCGLHB101

open LinnikCGLMat LinnikCGLReflect LinnikCGLPair LinnikCGLHBPos LinnikCGLHBLen LinnikCGLHBRefl LinnikCGLHBIter
  LinnikCGLT101 LinnikPower

/-- **Linnik's theorem with exponent `9/4`**: there is `K` such that for every `q ≥ 1` and every `a` prime to `q`
there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{9/4}` (`linnik_225c_t101` at `cglt101`). -/
theorem linnik_225 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLP81.linnik_225c_t101 cglt101

/-- **Linnik's theorem with exponent `226/100`**: there is `K` such that for every `q ≥ 1` and every `a` prime to `q`
there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{226/100}` (`linnik_226c_t101` at `cglt101`). -/
theorem linnik_226 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLP81.linnik_226c_t101 cglt101

end LinnikCGLHB101

namespace LinnikCGLDensity

open LinnikCGLStep

/-- **Linnik's theorem with exponent `9/4`**, `Linnik225C.linnik_225c` at `cglDensity`: there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{9/4}`. -/
theorem linnik_225c : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  Linnik225C.linnik_225c cglDensity

/-- **Linnik's theorem with exponent `226/100`**, `Linnik226C.linnik_226c` at `cglDensity`: there is `K` such that
for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{226/100}`. -/
theorem linnik_226c : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  Linnik226C.linnik_226c cglDensity

end LinnikCGLDensity

#print axioms LinnikCGLMat.linnik_225c_third
#print axioms LinnikCGLMat.linnik_226c_third
#print axioms LinnikCGLS23.linnik_225c_s23
#print axioms LinnikCGLS23.linnik_226c_s23
#print axioms LinnikCGLS2.linnik_225c_s3
#print axioms LinnikCGLS2.linnik_226c_s3
#print axioms LinnikCGLS3.linnik_225c_pt
#print axioms LinnikCGLS3.linnik_226c_pt
#print axioms LinnikCGLP81.linnik_225c_t101
#print axioms LinnikCGLP81.linnik_226c_t101
#print axioms LinnikCGLHB101.linnik_225
#print axioms LinnikCGLHB101.linnik_226
#print axioms LinnikCGLDensity.linnik_225c
#print axioms LinnikCGLDensity.linnik_226c
