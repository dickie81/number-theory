import CmMomData
-- alone: a kernel check that needs about 8 GiB of private memory; scripts/build.sh compiles it with nothing else

/-! # Kernel check of the moment chunk sum 3 (pieces 48–63) -/

namespace CmMom

theorem cs3_chk : decide (cs 3 = CS3) = true := by decide +kernel

end CmMom
