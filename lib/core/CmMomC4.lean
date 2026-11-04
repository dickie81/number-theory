import CmMomData

/-! # Kernel check of the moment chunk sum 4 (pieces 64–79) -/

namespace CmMom

theorem cs4_chk : decide (cs 4 = CS4) = true := by decide +kernel

end CmMom
