import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, even sector, rows 14–20 -/

namespace CmFin

theorem e14 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 14 = true := by decide +kernel
theorem e15 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 15 = true := by decide +kernel
theorem e16 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 16 = true := by decide +kernel
theorem e17 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 17 = true := by decide +kernel
theorem e18 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 18 = true := by decide +kernel
theorem e19 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 19 = true := by decide +kernel
theorem e20 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 20 = true := by decide +kernel

end CmFin
