import CmFinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds, odd sector at 6e-9, rows 14–20 -/

namespace CmFin

theorem p14 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 14 = true := by decide +kernel
theorem p15 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 15 = true := by decide +kernel
theorem p16 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 16 = true := by decide +kernel
theorem p17 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 17 = true := by decide +kernel
theorem p18 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 18 = true := by decide +kernel
theorem p19 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 19 = true := by decide +kernel
theorem p20 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 20 = true := by decide +kernel

end CmFin
