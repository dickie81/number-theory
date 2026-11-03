import CmFinD

/-! # Kernel checks of the entry bounds, even sector, rows 0–6 -/

namespace CmFin

theorem e0 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 0 = true := by decide +kernel
theorem e1 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 1 = true := by decide +kernel
theorem e2 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 2 = true := by decide +kernel
theorem e3 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 3 = true := by decide +kernel
theorem e4 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 4 = true := by decide +kernel
theorem e5 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 5 = true := by decide +kernel
theorem e6 : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) 6 = true := by decide +kernel

end CmFin
