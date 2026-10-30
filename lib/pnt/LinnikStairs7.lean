/-
# The staircase of the Weyl-conditional route (Ingham steps on `[4/7, 5/7]`, Huxley's on `[16/21, 11/12]`)

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Sixty density estimates, each an instance of a parametric argument of the library, and the count above `11/12`:

* `charDensity_in7_0` … `charDensity_in7_19`: `LinnikInghamC.charDensity_ingham_c` at `ε = 1/8000` on twenty equal
  steps `[σ₁, σ₂]` from `4/7` to `5/7`, with the exponent `3/(2 − σ₂) + 1/2000`, Ingham's curve at the right end plus
  `1/2000`.
* `parHx7_0` … `parHx7_19`, `charDensity_hx7_0` … `charDensity_hx7_19`: `LinnikHuxStep.charDensity_gen` at parameters
  found by a linear program and checked in rational arithmetic on twenty equal steps from `16/21` to `5/6`,
  with the exponent `3/(3σ₁ − 1) + 1/2000`, Huxley's curve at the left end plus `1/2000`.
* `parHy_0` … `parHy_19`, `charDensity_hy_0` … `charDensity_hy_19`: `LinnikHuxStepY.charDensity_genY`, under
  `LinnikWeyl.PYWeyl`, on twenty equal steps from `5/6` to `11/12`, with the exponent `3/(3σ₁ − 1) + 1/2000` on steps
  `1` to `19` and the least the step allows, `50159 / 25000`, on step `0` (where `3/(3σ₁ − 1) + 1/2000 = 4001/2000` is
  not reachable: the height `y ≥ 3(1/6 + 2ε + 1/2000)` and the first Huxley term force `A ≥ 4y + 2ε`).
* `card_le_one_of_gt`: above `11/12` at most one character is counted (the zero-free half-plane); `charDensity_hy_top`:
  the last step's exponent on `[73 / 80, 1]`, under `PYWeyl`.

The file imports `LinnikInghamC.lean`, `LinnikHuxStep.lean` and `LinnikHuxStepY.lean`.
-/
import LinnikInghamC
import LinnikHuxStep
import LinnikStairsGen
import LinnikHuxStepY

open Complex Real Finset

noncomputable section

namespace LinnikStairs7

open DirichletCharacter LinnikHuxStep LinnikHuxStepY

/-! ### Ingham's steps on `[4/7, 5/7]` -/

open scoped Classical in
/-- **Ingham's step `0`**: the exponent `840199 / 398000` on `[4 / 7, 81 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 81 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 11 / 398`, `δ₀ = 1 / 14`. -/
theorem charDensity_in7_0 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 4 / 7 ≤ σ → σ ≤ 81 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840199 / 398000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 11 / 398) (δ₀ := 1 / 14)
    (σ₂ := 81 / 140) (lo := 4 / 7) (A := 840199 / 398000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `1`**: the exponent `140033 / 66000` on `[81 / 140, 41 / 70]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 41 / 70`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 33`, `δ₀ = 11 / 140`. -/
theorem charDensity_in7_1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 81 / 140 ≤ σ → σ ≤ 41 / 70 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140033 / 66000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 1 / 33) (δ₀ := 11 / 140)
    (σ₂ := 41 / 70) (lo := 81 / 140) (A := 140033 / 66000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `2`**: the exponent `840197 / 394000` on `[41 / 70, 83 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 83 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 13 / 394`, `δ₀ = 3 / 35`. -/
theorem charDensity_in7_2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 41 / 70 ≤ σ → σ ≤ 83 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840197 / 394000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 13 / 394) (δ₀ := 3 / 35)
    (σ₂ := 83 / 140) (lo := 41 / 70) (A := 840197 / 394000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `3`**: the exponent `30007 / 14000` on `[83 / 140, 3 / 5]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 3 / 5`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 28`, `δ₀ = 13 / 140`. -/
theorem charDensity_in7_3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 83 / 140 ≤ σ → σ ≤ 3 / 5 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((30007 / 14000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 1 / 28) (δ₀ := 13 / 140)
    (σ₂ := 3 / 5) (lo := 83 / 140) (A := 30007 / 14000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `4`**: the exponent `56013 / 26000` on `[3 / 5, 17 / 28]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 17 / 28`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 26`, `δ₀ = 1 / 10`. -/
theorem charDensity_in7_4 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 3 / 5 ≤ σ → σ ≤ 17 / 28 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((56013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 1 / 26) (δ₀ := 1 / 10)
    (σ₂ := 17 / 28) (lo := 3 / 5) (A := 56013 / 26000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `5`**: the exponent `420097 / 194000` on `[17 / 28, 43 / 70]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 43 / 70`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 4 / 97`, `δ₀ = 3 / 28`. -/
theorem charDensity_in7_5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 17 / 28 ≤ σ → σ ≤ 43 / 70 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((420097 / 194000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 4 / 97) (δ₀ := 3 / 28)
    (σ₂ := 43 / 70) (lo := 17 / 28) (A := 420097 / 194000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `6`**: the exponent `840193 / 386000` on `[43 / 70, 87 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 87 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 17 / 386`, `δ₀ = 4 / 35`. -/
theorem charDensity_in7_6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 43 / 70 ≤ σ → σ ≤ 87 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840193 / 386000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 17 / 386) (δ₀ := 4 / 35)
    (σ₂ := 87 / 140) (lo := 43 / 70) (A := 840193 / 386000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `7`**: the exponent `547 / 250` on `[87 / 140, 22 / 35]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 22 / 35`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 3 / 64`, `δ₀ = 17 / 140`. -/
theorem charDensity_in7_7 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 87 / 140 ≤ σ → σ ≤ 22 / 35 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((547 / 250) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 3 / 64) (δ₀ := 17 / 140)
    (σ₂ := 22 / 35) (lo := 87 / 140) (A := 547 / 250)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `8`**: the exponent `840191 / 382000` on `[22 / 35, 89 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 89 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 19 / 382`, `δ₀ = 9 / 70`. -/
theorem charDensity_in7_8 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 22 / 35 ≤ σ → σ ≤ 89 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840191 / 382000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 19 / 382) (δ₀ := 9 / 70)
    (σ₂ := 89 / 140) (lo := 22 / 35) (A := 840191 / 382000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `9`**: the exponent `84019 / 38000` on `[89 / 140, 9 / 14]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 9 / 14`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 19`, `δ₀ = 19 / 140`. -/
theorem charDensity_in7_9 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 89 / 140 ≤ σ → σ ≤ 9 / 14 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((84019 / 38000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 1 / 19) (δ₀ := 19 / 140)
    (σ₂ := 9 / 14) (lo := 89 / 140) (A := 84019 / 38000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `10`**: the exponent `40009 / 18000` on `[9 / 14, 13 / 20]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 13 / 20`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 18`, `δ₀ = 1 / 7`. -/
theorem charDensity_in7_10 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 9 / 14 ≤ σ → σ ≤ 13 / 20 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((40009 / 18000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 1 / 18) (δ₀ := 1 / 7)
    (σ₂ := 13 / 20) (lo := 9 / 14) (A := 40009 / 18000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `11`**: the exponent `210047 / 94000` on `[13 / 20, 23 / 35]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 23 / 35`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 11 / 188`, `δ₀ = 3 / 20`. -/
theorem charDensity_in7_11 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 13 / 20 ≤ σ → σ ≤ 23 / 35 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((210047 / 94000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 11 / 188) (δ₀ := 3 / 20)
    (σ₂ := 23 / 35) (lo := 13 / 20) (A := 210047 / 94000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `12`**: the exponent `840187 / 374000` on `[23 / 35, 93 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 93 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 23 / 374`, `δ₀ = 11 / 70`. -/
theorem charDensity_in7_12 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 23 / 35 ≤ σ → σ ≤ 93 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840187 / 374000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 23 / 374) (δ₀ := 11 / 70)
    (σ₂ := 93 / 140) (lo := 23 / 35) (A := 840187 / 374000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `13`**: the exponent `140031 / 62000` on `[93 / 140, 47 / 70]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 47 / 70`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 2 / 31`, `δ₀ = 23 / 140`. -/
theorem charDensity_in7_13 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 93 / 140 ≤ σ → σ ≤ 47 / 70 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140031 / 62000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 2 / 31) (δ₀ := 23 / 140)
    (σ₂ := 47 / 70) (lo := 93 / 140) (A := 140031 / 62000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `14`**: the exponent `168037 / 74000` on `[47 / 70, 19 / 28]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 19 / 28`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 5 / 74`, `δ₀ = 6 / 35`. -/
theorem charDensity_in7_14 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 47 / 70 ≤ σ → σ ≤ 19 / 28 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((168037 / 74000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 5 / 74) (δ₀ := 6 / 35)
    (σ₂ := 19 / 28) (lo := 47 / 70) (A := 168037 / 74000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `15`**: the exponent `105023 / 46000` on `[19 / 28, 24 / 35]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 24 / 35`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 13 / 184`, `δ₀ = 5 / 28`. -/
theorem charDensity_in7_15 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 19 / 28 ≤ σ → σ ≤ 24 / 35 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((105023 / 46000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 13 / 184) (δ₀ := 5 / 28)
    (σ₂ := 24 / 35) (lo := 19 / 28) (A := 105023 / 46000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `16`**: the exponent `280061 / 122000` on `[24 / 35, 97 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 97 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 9 / 122`, `δ₀ = 13 / 70`. -/
theorem charDensity_in7_16 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 24 / 35 ≤ σ → σ ≤ 97 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280061 / 122000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 9 / 122) (δ₀ := 13 / 70)
    (σ₂ := 97 / 140) (lo := 24 / 35) (A := 280061 / 122000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `17`**: the exponent `60013 / 26000` on `[97 / 140, 7 / 10]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 7 / 10`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 13`, `δ₀ = 27 / 140`. -/
theorem charDensity_in7_17 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 97 / 140 ≤ σ → σ ≤ 7 / 10 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((60013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 1 / 13) (δ₀ := 27 / 140)
    (σ₂ := 7 / 10) (lo := 97 / 140) (A := 60013 / 26000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

open scoped Classical in
/-- **Ingham's step `18`**: the exponent `840181 / 362000` on `[7 / 10, 99 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 99 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 29 / 362`, `δ₀ = 1 / 5`. -/
theorem charDensity_in7_18 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 99 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840181 / 362000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikStairsGen.charDensity_ingham_inst (ε := 1 / 8000) (c := 29 / 362) (δ₀ := 1 / 5)
    (σ₂ := 99 / 140) (lo := 7 / 10) (A := 840181 / 362000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! ### Huxley's steps on `[16/21, 5/6]`, with the fourth moment -/

/-- The parameters of Huxley's step `5` on `[131 / 168, 47 / 60]`: the exponent `4481 / 2000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_5 : Par where
  M := 1495
  a := 18667 / 25000
  lam := 224009 / 200000
  lo := 131 / 168
  hi := 47 / 60
  Ai := 224049 / 100000
  A := 4481 / 2000

theorem parHx7_5_good : parHx7_5.Good := by stairs_good parHx7_5

open scoped Classical in
/-- **Huxley's step `5`**: there is `C ≥ 0` such that for every `q ≥ 1`, `131 / 168 ≤ σ ≤ 47 / 60` and `T ≥ 2` at most
`C(qT)^{(4481 / 2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 131 / 168 ≤ σ → σ ≤ 47 / 60 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((4481 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_5 parHx7_5_good

/-- The parameters of Huxley's step `6` on `[47 / 60, 661 / 840]`: the exponent `40009 / 18000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_6 : Par where
  M := 1483
  a := 2963 / 4000
  lam := 22223 / 20000
  lo := 47 / 60
  hi := 661 / 840
  Ai := 6946 / 3125
  A := 40009 / 18000

theorem parHx7_6_good : parHx7_6.Good := by stairs_good parHx7_6

open scoped Classical in
/-- **Huxley's step `6`**: there is `C ≥ 0` such that for every `q ≥ 1`, `47 / 60 ≤ σ ≤ 661 / 840` and `T ≥ 2` at most
`C(qT)^{(40009 / 18000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 47 / 60 ≤ σ → σ ≤ 661 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((40009 / 18000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_6 parHx7_6_good

/-- The parameters of Huxley's step `7` on `[661 / 840, 83 / 105]`: the exponent `560127 / 254000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_7 : Par where
  M := 1471
  a := 18373 / 25000
  lam := 220481 / 200000
  lo := 661 / 840
  hi := 83 / 105
  Ai := 110261 / 50000
  A := 560127 / 254000

theorem parHx7_7_good : parHx7_7.Good := by stairs_good parHx7_7

open scoped Classical in
/--  **Huxley's step `7`**: there is `C ≥ 0` such that for every `q ≥ 1`, `661 / 840 ≤ σ ≤ 83 / 105` and `T ≥ 2` at most
`C(qT)^{(560127 / 254000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx7_7 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 661 / 840 ≤ σ → σ ≤ 83 / 105 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560127 / 254000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_7 parHx7_7_good

/-- The parameters of Huxley's step `8` on `[83 / 105, 667 / 840]`: the exponent `547 / 250`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_8 : Par where
  M := 1460
  a := 36459 / 50000
  lam := 218759 / 200000
  lo := 83 / 105
  hi := 667 / 840
  Ai := 218799 / 100000
  A := 547 / 250

theorem parHx7_8_good : parHx7_8.Good := by stairs_good parHx7_8

open scoped Classical in
/-- **Huxley's step `8`**: there is `C ≥ 0` such that for every `q ≥ 1`, `83 / 105 ≤ σ ≤ 667 / 840` and `T ≥ 2` at most
`C(qT)^{(547 / 250)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_8 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 83 / 105 ≤ σ → σ ≤ 667 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((547 / 250) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_8 parHx7_8_good

/-- The parameters of Huxley's step `9` on `[667 / 840, 67 / 84]`: the exponent `560129 / 258000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_9 : Par where
  M := 1449
  a := 72353 / 100000
  lam := 27133 / 25000
  lo := 667 / 840
  hi := 67 / 84
  Ai := 13569 / 6250
  A := 560129 / 258000

theorem parHx7_9_good : parHx7_9.Good := by stairs_good parHx7_9

open scoped Classical in
/--  **Huxley's step `9`**: there is `C ≥ 0` such that for every `q ≥ 1`, `667 / 840 ≤ σ ≤ 67 / 84` and `T ≥ 2` at most
`C(qT)^{(560129 / 258000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx7_9 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 667 / 840 ≤ σ → σ ≤ 67 / 84 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560129 / 258000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_9 parHx7_9_good

/-- The parameters of Huxley's step `10` on `[67 / 84, 673 / 840]`: the exponent `56013 / 26000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_10 : Par where
  M := 1437
  a := 17949 / 25000
  lam := 215393 / 200000
  lo := 67 / 84
  hi := 673 / 840
  Ai := 107717 / 50000
  A := 56013 / 26000

theorem parHx7_10_good : parHx7_10.Good := by stairs_good parHx7_10

open scoped Classical in
/-- **Huxley's step `10`**: there is `C ≥ 0` such that for every `q ≥ 1`, `67 / 84 ≤ σ ≤ 673 / 840` and `T ≥ 2` at most
`C(qT)^{(56013 / 26000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_10 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 67 / 84 ≤ σ → σ ≤ 673 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((56013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_10 parHx7_10_good

/-- The parameters of Huxley's step `11` on `[673 / 840, 169 / 210]`: the exponent `560131 / 262000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_11 : Par where
  M := 1426
  a := 4453 / 6250
  lam := 213749 / 200000
  lo := 673 / 840
  hi := 169 / 210
  Ai := 21379 / 10000
  A := 560131 / 262000

theorem parHx7_11_good : parHx7_11.Good := by stairs_good parHx7_11

open scoped Classical in
/--  **Huxley's step `11`**: there is `C ≥ 0` such that for every `q ≥ 1`, `673 / 840 ≤ σ ≤ 169 / 210` and `T ≥ 2` at
most `C(qT)^{(560131 / 262000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_11 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 673 / 840 ≤ σ → σ ≤ 169 / 210 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560131 / 262000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_11 parHx7_11_good

/-- The parameters of Huxley's step `12` on `[169 / 210, 97 / 120]`: the exponent `140033 / 66000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_12 : Par where
  M := 1416
  a := 17677 / 25000
  lam := 212129 / 200000
  lo := 169 / 210
  hi := 97 / 120
  Ai := 212171 / 100000
  A := 140033 / 66000

theorem parHx7_12_good : parHx7_12.Good := by stairs_good parHx7_12

open scoped Classical in
/-- **Huxley's step `12`**: there is `C ≥ 0` such that for every `q ≥ 1`, `169 / 210 ≤ σ ≤ 97 / 120` and `T ≥ 2` at most
`C(qT)^{(140033 / 66000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_12 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 169 / 210 ≤ σ → σ ≤ 97 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140033 / 66000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_12 parHx7_12_good

/-- The parameters of Huxley's step `13` on `[97 / 120, 341 / 420]`: the exponent `80019 / 38000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_13 : Par where
  M := 1405
  a := 70177 / 100000
  lam := 26317 / 25000
  lo := 97 / 120
  hi := 341 / 420
  Ai := 13161 / 6250
  A := 80019 / 38000

theorem parHx7_13_good : parHx7_13.Good := by stairs_good parHx7_13

open scoped Classical in
/-- **Huxley's step `13`**: there is `C ≥ 0` such that for every `q ≥ 1`, `97 / 120 ≤ σ ≤ 341 / 420` and `T ≥ 2` at most
`C(qT)^{(80019 / 38000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_13 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 97 / 120 ≤ σ → σ ≤ 341 / 420 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((80019 / 38000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_13 parHx7_13_good

/-- The parameters of Huxley's step `14` on `[341 / 420, 137 / 168]`: the exponent `280067 / 134000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_14 : Par where
  M := 1395
  a := 69653 / 100000
  lam := 52241 / 50000
  lo := 341 / 420
  hi := 137 / 168
  Ai := 41801 / 20000
  A := 280067 / 134000

theorem parHx7_14_good : parHx7_14.Good := by stairs_good parHx7_14

open scoped Classical in
/--  **Huxley's step `14`**: there is `C ≥ 0` such that for every `q ≥ 1`, `341 / 420 ≤ σ ≤ 137 / 168` and `T ≥ 2` at
most `C(qT)^{(280067 / 134000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_14 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 341 / 420 ≤ σ → σ ≤ 137 / 168 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280067 / 134000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_14 parHx7_14_good

/-- The parameters of Huxley's step `15` on `[137 / 168, 86 / 105]`: the exponent `112027 / 54000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_15 : Par where
  M := 1384
  a := 69137 / 100000
  lam := 25927 / 25000
  lo := 137 / 168
  hi := 86 / 105
  Ai := 207457 / 100000
  A := 112027 / 54000

theorem parHx7_15_good : parHx7_15.Good := by stairs_good parHx7_15

open scoped Classical in
/-- **Huxley's step `15`**: there is `C ≥ 0` such that for every `q ≥ 1`, `137 / 168 ≤ σ ≤ 86 / 105` and `T ≥ 2` at most
`C(qT)^{(112027 / 54000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_15 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 137 / 168 ≤ σ → σ ≤ 86 / 105 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((112027 / 54000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_15 parHx7_15_good

/-- The parameters of Huxley's step `16` on `[86 / 105, 691 / 840]`: the exponent `70017 / 34000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_16 : Par where
  M := 1374
  a := 17157 / 25000
  lam := 205889 / 200000
  lo := 86 / 105
  hi := 691 / 840
  Ai := 51483 / 25000
  A := 70017 / 34000

theorem parHx7_16_good : parHx7_16.Good := by stairs_good parHx7_16

open scoped Classical in
/-- **Huxley's step `16`**: there is `C ≥ 0` such that for every `q ≥ 1`, `86 / 105 ≤ σ ≤ 691 / 840` and `T ≥ 2` at most
`C(qT)^{(70017 / 34000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_16 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 86 / 105 ≤ σ → σ ≤ 691 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((70017 / 34000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_16 parHx7_16_good

/-- The parameters of Huxley's step `17` on `[691 / 840, 347 / 420]`: the exponent `560137 / 274000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_17 : Par where
  M := 1364
  a := 2129 / 3125
  lam := 204389 / 200000
  lo := 691 / 840
  hi := 347 / 420
  Ai := 204429 / 100000
  A := 560137 / 274000

theorem parHx7_17_good : parHx7_17.Good := by stairs_good parHx7_17

open scoped Classical in
/--  **Huxley's step `17`**: there is `C ≥ 0` such that for every `q ≥ 1`, `691 / 840 ≤ σ ≤ 347 / 420` and `T ≥ 2` at
most `C(qT)^{(560137 / 274000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_17 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 691 / 840 ≤ σ → σ ≤ 347 / 420 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560137 / 274000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_17 parHx7_17_good

/-- The parameters of Huxley's step `18` on `[347 / 420, 697 / 840]`: the exponent `280069 / 138000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_18 : Par where
  M := 1354
  a := 33817 / 50000
  lam := 202907 / 200000
  lo := 347 / 420
  hi := 697 / 840
  Ai := 50737 / 25000
  A := 280069 / 138000

theorem parHx7_18_good : parHx7_18.Good := by stairs_good parHx7_18

open scoped Classical in
/--  **Huxley's step `18`**: there is `C ≥ 0` such that for every `q ≥ 1`, `347 / 420 ≤ σ ≤ 697 / 840` and `T ≥ 2` at
most `C(qT)^{(280069 / 138000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_18 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 347 / 420 ≤ σ → σ ≤ 697 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280069 / 138000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_18 parHx7_18_good

/-- The parameters of Huxley's step `19` on `[697 / 840, 5 / 6]`: the exponent `560139 / 278000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_19 : Par where
  M := 1344
  a := 67147 / 100000
  lam := 100723 / 100000
  lo := 697 / 840
  hi := 5 / 6
  Ai := 12593 / 6250
  A := 560139 / 278000

theorem parHx7_19_good : parHx7_19.Good := by stairs_good parHx7_19

open scoped Classical in
/--  **Huxley's step `19`**: there is `C ≥ 0` such that for every `q ≥ 1`, `697 / 840 ≤ σ ≤ 5 / 6` and `T ≥ 2` at most
`C(qT)^{(560139 / 278000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx7_19 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 697 / 840 ≤ σ → σ ≤ 5 / 6 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_19 parHx7_19_good

/-! ### The steps on `[5/6, 11/12]`, under the pointwise bound -/

/-- The parameters of the step `0` above `5/6`, on `[5 / 6, 67 / 80]`: the exponent `50159 / 25000`, the
height `y = 12539 / 25000` (`cy = 25053 / 50`), under the pointwise bound. -/
def parHy_0 : ParY where
  M := 1333
  a := 16641 / 25000
  lam := 50157 / 50000
  lo := 5 / 6
  hi := 67 / 80
  Ai := 40127 / 20000
  A := 50159 / 25000
  cy := 25053 / 50

theorem parHy_0_good : parHy_0.Good := by stairs_good_y parHy_0

open scoped Classical in
/-- **The step `0` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `5 / 6 ≤ σ ≤ 67 / 80`
and `T ≥ 2` at most `C(qT)^{(50159 / 25000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_0 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 6 ≤ σ → σ ≤ 67 / 80 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((50159 / 25000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_0 parHy_0_good hPY

/-- The parameters of the step `19` above `5/6`, on `[73 / 80, 11 / 12]`: the exponent `480139 / 278000`, the
height `y = 40531 / 100000` (`cy = 40481 / 100`), under the pointwise bound. -/
def parHy_19 : ParY where
  M := 1153
  a := 11511 / 20000
  lam := 17267 / 20000
  lo := 73 / 80
  hi := 11 / 12
  Ai := 172711 / 100000
  A := 480139 / 278000
  cy := 40481 / 100

theorem parHy_19_good : parHy_19.Good := by stairs_good_y parHy_19

open scoped Classical in
/-- **The step `19` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `73 / 80 ≤ σ ≤ 11 / 12`
and `T ≥ 2` at most `C(qT)^{(480139 / 278000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_19 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 73 / 80 ≤ σ → σ ≤ 11 / 12 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_19 parHy_19_good hPY

/-! ### Above `11/12` -/

open scoped Classical in
/-- **Above `11/12` the count is at most `1`**: by the zero-free half-plane `Re s > 11/12`
(`LinnikLindelof.LFunction_ne_zero`), only the trivial character can be counted. -/
theorem card_le_one_of_gt {q : ℕ} [NeZero q] {σ T : ℝ} (hσ : 11 / 12 < σ) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ 1 := by
  have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) ⊆ {1} := by
    intro χ hχ
    rw [Finset.mem_singleton]
    by_contra h1
    obtain ⟨-, s, hs, -, hz⟩ := Finset.mem_filter.1 hχ
    exact LinnikLindelof.LFunction_ne_zero h1 (by linarith) hz
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_singleton _).le

open scoped Classical in
/--  **The last step, extended to `σ ≤ 1`, under `PYWeyl`**: the exponent `480139 / 278000` on `[73 / 80, 1]`; above
`11/12` the count is at most `1` (`card_le_one_of_gt`), and `1 ≤ 2^{10}(qT)^{E}(log qT)^{10}` since `log qT ≥ 1/2`. -/
theorem charDensity_hy_top (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 73 / 80 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := charDensity_hy_19 hPY
  refine ⟨C + 2 ^ 10, by positivity, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) hqT
  have hℓ : 1 / 2 ≤ Real.log ((q : ℝ) * T) := by have := Real.log_two_gt_d9; linarith
  have hE0 : 0 ≤ (480139 / 278000) * (1 - σ) := by nlinarith
  have hP1 : 1 ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) := Real.one_le_rpow (by linarith) hE0
  have hℓ10 : 1 ≤ 2 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hℓ (by norm_num : (0 : ℝ) ≤ 10)
    have h2 : (2 : ℝ) ^ 10 * (1 / 2 : ℝ) ^ (10 : ℝ) = 1 := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    nlinarith
  have hP : 0 ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by positivity
  have h1 : 1 ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * (2 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hP1 hℓ10
  rcases le_or_gt σ (11 / 12) with hle | hgt
  · calc _ ≤ C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
          hC q σ T hσ hle hT
      _ ≤ (C + 2 ^ 10) * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
          nlinarith
  · have hrest : 0 ≤ C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
      positivity
    calc _ ≤ (1 : ℝ) := card_le_one_of_gt hgt
      _ ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * (2 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) := h1
      _ ≤ (C + 2 ^ 10) * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
          linarith

end LinnikStairs7

#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_hy_0
#print axioms LinnikStairs7.charDensity_hy_top
