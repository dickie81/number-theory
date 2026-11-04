import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, odd sector at 6e-9, rows 7–13 -/

namespace CmFin

theorem p7 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 7 = true := by decide +kernel
theorem p8 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 8 = true := by decide +kernel
theorem p9 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 9 = true := by decide +kernel
theorem p10 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 10 = true := by decide +kernel
theorem p11 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 11 = true := by decide +kernel
theorem p12 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 12 = true := by decide +kernel
theorem p13 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 13 = true := by decide +kernel

end CmFin
