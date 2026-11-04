import V3FinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds at `λ = log 3`, odd sector, rows 8–27 (upper triangle) -/

namespace V3Fin

theorem o8 : rowOK3 1 cqO (3 / 10 ^ 9) 8 = true := by decide +kernel
theorem o9 : rowOK3 1 cqO (3 / 10 ^ 9) 9 = true := by decide +kernel
theorem o10 : rowOK3 1 cqO (3 / 10 ^ 9) 10 = true := by decide +kernel
theorem o11 : rowOK3 1 cqO (3 / 10 ^ 9) 11 = true := by decide +kernel
theorem o12 : rowOK3 1 cqO (3 / 10 ^ 9) 12 = true := by decide +kernel
theorem o13 : rowOK3 1 cqO (3 / 10 ^ 9) 13 = true := by decide +kernel
theorem o14 : rowOK3 1 cqO (3 / 10 ^ 9) 14 = true := by decide +kernel
theorem o15 : rowOK3 1 cqO (3 / 10 ^ 9) 15 = true := by decide +kernel
theorem o16 : rowOK3 1 cqO (3 / 10 ^ 9) 16 = true := by decide +kernel
theorem o17 : rowOK3 1 cqO (3 / 10 ^ 9) 17 = true := by decide +kernel
theorem o18 : rowOK3 1 cqO (3 / 10 ^ 9) 18 = true := by decide +kernel
theorem o19 : rowOK3 1 cqO (3 / 10 ^ 9) 19 = true := by decide +kernel
theorem o20 : rowOK3 1 cqO (3 / 10 ^ 9) 20 = true := by decide +kernel
theorem o21 : rowOK3 1 cqO (3 / 10 ^ 9) 21 = true := by decide +kernel
theorem o22 : rowOK3 1 cqO (3 / 10 ^ 9) 22 = true := by decide +kernel
theorem o23 : rowOK3 1 cqO (3 / 10 ^ 9) 23 = true := by decide +kernel
theorem o24 : rowOK3 1 cqO (3 / 10 ^ 9) 24 = true := by decide +kernel
theorem o25 : rowOK3 1 cqO (3 / 10 ^ 9) 25 = true := by decide +kernel
theorem o26 : rowOK3 1 cqO (3 / 10 ^ 9) 26 = true := by decide +kernel
theorem o27 : rowOK3 1 cqO (3 / 10 ^ 9) 27 = true := by decide +kernel

end V3Fin
