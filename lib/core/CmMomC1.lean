import CmMomData
-- alone: a kernel check that needs about 8 GiB of private memory; scripts/build.sh compiles it with nothing else

/-! # Kernel check of the moment chunk sum 1 (pieces 16–31) -/

namespace CmMom

theorem cs1_chk : decide (cs 1 = CS1) = true := by decide +kernel

end CmMom
