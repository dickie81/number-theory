import CmMomData

/-! # Kernel check of the moment chunk sum 7 (pieces 112–127) -/

namespace CmMom

theorem cs7_chk : decide (cs 7 = CS7) = true := by decide +kernel

end CmMom
