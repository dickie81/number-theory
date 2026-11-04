import CmMomData

/-! # Kernel check of the moment chunk sum 5 (pieces 80–95) -/

namespace CmMom

theorem cs5_chk : decide (cs 5 = CS5) = true := by decide +kernel

end CmMom
