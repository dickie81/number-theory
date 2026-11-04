import CmMomData

/-! # Kernel check of the moment chunk sum 3 (pieces 48–63) -/

namespace CmMom

theorem cs3_chk : decide (cs 3 = CS3) = true := by decide +kernel

end CmMom
