import CmMomData

/-! # Kernel check of the moment chunk sum 1 (pieces 16–31) -/

namespace CmMom

theorem cs1_chk : decide (cs 1 = CS1) = true := by decide +kernel

end CmMom
