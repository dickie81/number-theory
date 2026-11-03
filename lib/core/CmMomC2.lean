import CmMomData

/-! # Kernel check of the moment chunk sum 2 (pieces 32–47) -/

namespace CmMom

theorem cs2_chk : decide (cs 2 = CS2) = true := by decide +kernel

end CmMom
