import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, odd sector, rows 0–6 -/

namespace CmFin

theorem o0 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 0 = true := by decide +kernel
theorem o1 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 1 = true := by decide +kernel
theorem o2 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 2 = true := by decide +kernel
theorem o3 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 3 = true := by decide +kernel
theorem o4 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 4 = true := by decide +kernel
theorem o5 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 5 = true := by decide +kernel
theorem o6 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 6 = true := by decide +kernel

end CmFin
