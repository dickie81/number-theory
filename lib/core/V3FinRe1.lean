import V3FinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds at `λ = log 3`, even sector, rows 8–27 (upper triangle) -/

namespace V3Fin

theorem e8 : rowOK3 0 cqE (3 / 10 ^ 9) 8 = true := by decide +kernel
theorem e9 : rowOK3 0 cqE (3 / 10 ^ 9) 9 = true := by decide +kernel
theorem e10 : rowOK3 0 cqE (3 / 10 ^ 9) 10 = true := by decide +kernel
theorem e11 : rowOK3 0 cqE (3 / 10 ^ 9) 11 = true := by decide +kernel
theorem e12 : rowOK3 0 cqE (3 / 10 ^ 9) 12 = true := by decide +kernel
theorem e13 : rowOK3 0 cqE (3 / 10 ^ 9) 13 = true := by decide +kernel
theorem e14 : rowOK3 0 cqE (3 / 10 ^ 9) 14 = true := by decide +kernel
theorem e15 : rowOK3 0 cqE (3 / 10 ^ 9) 15 = true := by decide +kernel
theorem e16 : rowOK3 0 cqE (3 / 10 ^ 9) 16 = true := by decide +kernel
theorem e17 : rowOK3 0 cqE (3 / 10 ^ 9) 17 = true := by decide +kernel
theorem e18 : rowOK3 0 cqE (3 / 10 ^ 9) 18 = true := by decide +kernel
theorem e19 : rowOK3 0 cqE (3 / 10 ^ 9) 19 = true := by decide +kernel
theorem e20 : rowOK3 0 cqE (3 / 10 ^ 9) 20 = true := by decide +kernel
theorem e21 : rowOK3 0 cqE (3 / 10 ^ 9) 21 = true := by decide +kernel
theorem e22 : rowOK3 0 cqE (3 / 10 ^ 9) 22 = true := by decide +kernel
theorem e23 : rowOK3 0 cqE (3 / 10 ^ 9) 23 = true := by decide +kernel
theorem e24 : rowOK3 0 cqE (3 / 10 ^ 9) 24 = true := by decide +kernel
theorem e25 : rowOK3 0 cqE (3 / 10 ^ 9) 25 = true := by decide +kernel
theorem e26 : rowOK3 0 cqE (3 / 10 ^ 9) 26 = true := by decide +kernel
theorem e27 : rowOK3 0 cqE (3 / 10 ^ 9) 27 = true := by decide +kernel

end V3Fin
