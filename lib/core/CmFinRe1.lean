import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, even sector, rows 7–13 -/

namespace CmFin

theorem e7 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 7 = true := by decide +kernel
theorem e8 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 8 = true := by decide +kernel
theorem e9 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 9 = true := by decide +kernel
theorem e10 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 10 = true := by decide +kernel
theorem e11 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 11 = true := by decide +kernel
theorem e12 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 12 = true := by decide +kernel
theorem e13 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 13 = true := by decide +kernel

end CmFin
