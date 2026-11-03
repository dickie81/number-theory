import CmMomData

/-! # Kernel check of the moment chunk sum 0 (pieces 0–15) -/

namespace CmMom

theorem cs0_chk : decide (cs 0 = CS0) = true := by decide +kernel

end CmMom
