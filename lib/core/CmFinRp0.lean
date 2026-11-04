import CmFinD

/-! # Kernel checks of the entry bounds, odd sector at 6e-9, rows 0–6 -/

namespace CmFin

theorem p0 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 0 = true := by decide +kernel
theorem p1 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 1 = true := by decide +kernel
theorem p2 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 2 = true := by decide +kernel
theorem p3 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 3 = true := by decide +kernel
theorem p4 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 4 = true := by decide +kernel
theorem p5 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 5 = true := by decide +kernel
theorem p6 : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) 6 = true := by decide +kernel

end CmFin
