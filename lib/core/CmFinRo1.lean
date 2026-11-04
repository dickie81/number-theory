import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, odd sector, rows 7–13 -/

namespace CmFin

theorem o7 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 7 = true := by decide +kernel
theorem o8 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 8 = true := by decide +kernel
theorem o9 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 9 = true := by decide +kernel
theorem o10 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 10 = true := by decide +kernel
theorem o11 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 11 = true := by decide +kernel
theorem o12 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 12 = true := by decide +kernel
theorem o13 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 13 = true := by decide +kernel

end CmFin
