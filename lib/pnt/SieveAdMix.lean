/-
# The window's tests and the estimate's, together, are sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. In `SieveQ`'s setting (a route with `RouteOK`, a grid with `GridOK`, the two fitting, the bilinear
rule's exponent the route's, and the route's Type II estimate `hII`):

* `mixTests_sound`: the tests `SieveAd.mixTests` are sound (`SieveAd.Tests.Sound`), by `SieveAd.winTests_sound`
  for the configurations of kind `0` and `SieveAd.twoTests_sound` for the others.
* `mixTests_soundX`: they are sound under two more atoms, on the boxes of at most twelve primes
  (`SieveAd.Tests.SoundX`).

The file imports `SieveAdWin.lean`, `SieveAdTwo.lean` and `SieveAdMixDefs.lean`.
-/
import SieveAdWin
import SieveAdTwo
import SieveAdMixDefs

open SieveQ SieveRoute

namespace SieveAd

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] [SieveCert.IBPar] [IBFits]

/-- **The window's tests and the estimate's, together, are sound.** -/
theorem mixTests_sound (hII : TypeIIAt) : (mixTests).Sound := by
  refine ⟨fun bl cfg k' h hok => ?_, fun bl f cfg k h hok => ?_⟩
  · simp only [mixTests] at hok
    cases hk : Nat.beq cfg.kind 0
    · rw [hk] at hok
      exact twoTests_sound.soundI bl cfg k' h hok
    · rw [hk] at hok
      exact (winTests_sound hII).soundI bl cfg k' h hok
  · simp only [mixTests] at hok
    cases hk : Nat.beq cfg.kind 0
    · rw [hk] at hok
      exact twoTests_sound.soundJ bl f cfg k h hok
    · rw [hk] at hok
      exact (winTests_sound hII).soundJ bl f cfg k h hok

/-- **The window's tests and the estimate's, together, are sound under two more atoms**, on the boxes of at most
twelve primes. -/
theorem mixTests_soundX (hII : TypeIIAt) : (mixTests).SoundX := by
  refine ⟨fun bl cfg k' h hk hok => ?_, fun bl f cfg k h hk hok => ?_⟩
  · simp only [mixTests] at hok
    cases hk0 : Nat.beq cfg.kind 0
    · rw [hk0] at hok
      exact twoTests_soundX.soundI bl cfg k' h hk hok
    · rw [hk0] at hok
      exact (winTests_soundX hII).soundI bl cfg k' h hk hok
  · simp only [mixTests] at hok
    cases hk0 : Nat.beq cfg.kind 0
    · rw [hk0] at hok
      exact twoTests_soundX.soundJ bl f cfg k h hk hok
    · rw [hk0] at hok
      exact (winTests_soundX hII).soundJ bl f cfg k h hk hok

end SieveAd
