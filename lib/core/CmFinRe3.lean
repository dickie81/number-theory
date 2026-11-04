import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, even sector, rows 21–27 -/

namespace CmFin

theorem e21 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 21 = true := by decide +kernel
theorem e22 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 22 = true := by decide +kernel
theorem e23 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 23 = true := by decide +kernel
theorem e24 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 24 = true := by decide +kernel
theorem e25 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 25 = true := by decide +kernel
theorem e26 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 26 = true := by decide +kernel
theorem e27 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 27 = true := by decide +kernel

end CmFin
