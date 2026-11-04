import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, odd sector at 6e-9, rows 21–27 -/

namespace CmFin

theorem p21 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 21 = true := by decide +kernel
theorem p22 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 22 = true := by decide +kernel
theorem p23 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 23 = true := by decide +kernel
theorem p24 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 24 = true := by decide +kernel
theorem p25 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 25 = true := by decide +kernel
theorem p26 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 26 = true := by decide +kernel
theorem p27 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 27 = true := by decide +kernel

end CmFin
