import CmMomData
-- alone: a kernel check that needs about 8 GiB of private memory; scripts/build.sh compiles it with nothing else

/-! # Kernel check of the moment chunk sum 6 (pieces 96–111) -/

namespace CmMom

theorem cs6_chk : decide (cs 6 = CS6) = true := by decide +kernel

end CmMom
