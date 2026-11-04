import CmMomData
-- alone: a kernel check that needs about 8 GiB of private memory; scripts/build.sh compiles it with nothing else

/-! # Kernel check of the moment chunk sum 5 (pieces 80–95) -/

namespace CmMom

theorem cs5_chk : decide (cs 5 = CS5) = true := by decide +kernel

end CmMom
