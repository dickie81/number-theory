/-
# The tests in one pass with the paper's conditions on the leaves alone

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The lemmas of `SieveAdFast.lean` on the tests that read the leaves' conditions, as they stood at commit `40411d7`,
for the tests of `SieveAdPlainDefs.lean`, in the namespace `SieveAd.Plain`: the tests of the main tree in one pass
are the tests that are proved sound (`fillTestsF_eq`), and those over a frozen part imply the proved ones on the
boxes of its tree (`frozTestsC_okI`, `frozTestsC_okJ`). The lemmas that do not read the leaves' test are
`SieveAdFast.lean`'s own.

Its declarations: `coreJ3_eq`, `coreJ2_eq`, `okJ2F_eq`, `okJ3F_eq`, `fillTestsF_eq`, `okJF3C_imp`, `okJF2C_imp`,
`frozTestsC_okI`, `frozTestsC_okJ`.

The file imports `SieveAdFast.lean` and `SieveAdPlainDefs.lean`.
-/
import SieveAdFast
import SieveAdPlainDefs

namespace SieveAd.Plain

open SieveCert (DEN cdiv)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

theorem coreJ3_eq (f : ℕ) (e : Bool) (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) :
    coreJ3 f e u v t r1 r2 c0lo c0hi h1s h2s = (Nat.blt 0 f && coreJ3P f e u v t r1 r2 c0lo c0hi h1s h2s) := by
  simp only [coreJ3, coreJ3P, zoneJP, leavesP, Bool.and_assoc]
  rfl

theorem coreJ2_eq (f : ℕ) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) :
    coreJ2 f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s = (Nat.blt 0 f && coreJ2P f e u v t ρ₁ ρ₂ c0lo c0hi h1s h2s) := by
  simp only [coreJ2, coreJ2P, zoneJP, leavesP, Bool.and_assoc]
  rfl

theorem okJ2F_eq (bl : List Cell) (f : ℕ) (cfg : Cfg) : okJ2F bl f cfg = okJ2 bl f cfg := by
  unfold okJ2F
  rw [bpass_eq]
  simp only [Nat.zero_add]
  by_cases h : bl.length ≤ 13
  · rw [List.take_of_length_le h, cellsP_eq, uOfP_eq, vOfP_eq]
    simp only [okJ2, chkJ2, coreJ2P, zoneJP, leavesP, Bool.and_assoc]
    rfl
  · simp only [okJ2, chkJ2, ble_false_of_not_le h, Bool.false_and, Bool.and_false]

theorem okJ3F_eq (bl : List Cell) (f : ℕ) (cfg : Cfg) : okJ3F bl f cfg = okJ3 bl f cfg := by
  unfold okJ3F
  rw [bpass_eq]
  simp only [Nat.zero_add]
  by_cases h : bl.length ≤ 13
  · rw [List.take_of_length_le h, cellsP_eq, uOfP_eq, vOfP_eq]
    simp only [okJ3, chkJ3, coreJ3P, zoneJP, leavesP, Bool.and_assoc]
    rfl
  · simp only [okJ3, chkJ3, ble_false_of_not_le h, Bool.false_and, Bool.and_false]

/-- **The tests with no window in one pass are `fillTests`.** -/
theorem fillTestsF_eq : (fillTestsF : Tests) = fillTests := by
  unfold fillTestsF fillTests
  congr 1
  · funext bl cfg
    exact okI2F_eq bl cfg
  · funext bl f cfg
    rw [okJ3F_eq, okJ2F_eq]

/-- **`okJF3C` implies `okJF3`** on a box that is a chain followed by the frozen primes, whose cells pass the
check, for `lomβ` their least lower end. -/
theorem okJF3C_imp (e₁ e₂ Kb : ℕ) (β ch : List Cell) (f : ℕ) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : okJF3C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg = true) :
    okJF3 e₁ e₂ Kb β (ch ++ β) f cfg = true := by
  unfold okJF3C at h
  simp only [lenR_app_sub] at h
  rw [cpass_eq] at h
  simp only [canonN_eq, roleB, msumP_eq, cofP_eq, Nat.zero_add, List.take_left' rfl, cellsP_eq, uOfP_eq, vOfP_eq,
    Nat.pow_zero, Nat.div_one] at h
  simp only [okJF3, coreJ3_eq, loR, hiR, hiRc, chainOf_app, cellsFrom_append]
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hA, hC⟩, hL⟩, hcore⟩ := h
  rw [Nat.ble_eq] at hL
  exact ⟨⟨hA, hC, (cellsFrom_of_lomP β DEN hβ hL).1⟩, hA, hcore⟩

/-- **`okJF2C` implies `okJF2`** on a box that is a chain followed by the frozen primes, whose cells pass the
check, for `lomβ` their least lower end. -/
theorem okJF2C_imp (e₁ e₂ Kb : ℕ) (β ch : List Cell) (f : ℕ) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : okJF2C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg = true) :
    okJF2 e₁ e₂ Kb β (ch ++ β) f cfg = true := by
  unfold okJF2C at h
  simp only [lenR_app_sub] at h
  rw [cpass_eq] at h
  simp only [canonN_eq, roleB, msumP_eq, cofP_eq, Nat.zero_add, List.take_left' rfl, cellsP_eq, uOfP_eq, vOfP_eq,
    Nat.pow_zero, Nat.div_one] at h
  simp only [okJF2, coreJ2_eq, loR, hiR, hiRc, chainOf_app, cellsFrom_append]
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨hA, hC⟩, hL⟩, hS⟩, hR⟩, hcore⟩ := h
  rw [Nat.ble_eq] at hL
  exact ⟨⟨⟨⟨hA, hC, (cellsFrom_of_lomP β DEN hβ hL).1⟩, hS⟩, hR⟩, hA, hcore⟩

/-- **The tests that read the frozen primes once for each tree imply `frozTests`**, on a box that is a chain
followed by the frozen primes, whose cells pass the check: for the term of the box. -/
theorem frozTestsC_okI (e₁ e₂ Kb : ℕ) (β ch : List Cell) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : (frozTestsC e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)).okI (ch ++ β) cfg = true) :
    (frozTests e₁ e₂ Kb β).okI (ch ++ β) cfg = true :=
  okIFC_imp e₁ e₂ β ch cfg hβ h

/-- The same for the terms at a floor. -/
theorem frozTestsC_okJ (e₁ e₂ Kb : ℕ) (β ch : List Cell) (f : ℕ) (cfg : Cfg) (hβ : cellsFrom 1 β = true)
    (h : (frozTestsC e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN)).okJ (ch ++ β) f cfg = true) :
    (frozTests e₁ e₂ Kb β).okJ (ch ++ β) f cfg = true := by
  have h' : cond (Nat.beq cfg.kind 2) (okJF3C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg)
      (okJF2C e₁ e₂ Kb β (loSum β) (hiSum β) β.length (lomP β DEN) (ch ++ β) f cfg) = true := h
  show cond (Nat.beq cfg.kind 2) (okJF3 e₁ e₂ Kb β (ch ++ β) f cfg) (okJF2 e₁ e₂ Kb β (ch ++ β) f cfg) = true
  cases hk : Nat.beq cfg.kind 2 with
  | true =>
    rw [hk] at h'
    exact okJF3C_imp e₁ e₂ Kb β ch f cfg hβ h'
  | false =>
    rw [hk] at h'
    exact okJF2C_imp e₁ e₂ Kb β ch f cfg hβ h'

end SieveAd.Plain
