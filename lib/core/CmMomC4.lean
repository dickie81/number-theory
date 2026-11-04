import CmMomData
-- alone: a kernel check that needs about 8 GiB of private memory; scripts/build.sh compiles it with nothing else

/-! # Kernel check of the moment chunk sum 4 (pieces 64–79) -/

namespace CmMom

theorem cs4_chk : decide (cs 4 = CS4) = true := by decide +kernel

end CmMom
