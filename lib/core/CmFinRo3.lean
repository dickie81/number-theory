import CmFinD

/-! # Kernel checks of the entry bounds, odd sector, rows 21–27 -/

namespace CmFin

theorem o21 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 21 = true := by decide +kernel
theorem o22 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 22 = true := by decide +kernel
theorem o23 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 23 = true := by decide +kernel
theorem o24 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 24 = true := by decide +kernel
theorem o25 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 25 = true := by decide +kernel
theorem o26 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 26 = true := by decide +kernel
theorem o27 : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) 27 = true := by decide +kernel

end CmFin
