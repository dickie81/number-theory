import CmFinD

/-! # Kernel checks of the entry bounds, odd sector, rows 14–20 -/

namespace CmFin

theorem o14 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 14 = true := by decide +kernel
theorem o15 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 15 = true := by decide +kernel
theorem o16 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 16 = true := by decide +kernel
theorem o17 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 17 = true := by decide +kernel
theorem o18 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 18 = true := by decide +kernel
theorem o19 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 19 = true := by decide +kernel
theorem o20 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 20 = true := by decide +kernel

end CmFin
