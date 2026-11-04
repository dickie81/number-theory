import V3FinD
-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Kernel checks of the entry bounds at `λ = log 3`, even sector, rows 0–7 (upper triangle) -/

namespace V3Fin

theorem e0 : rowOK3 0 cqE (3 / 10 ^ 9) 0 = true := by decide +kernel
theorem e1 : rowOK3 0 cqE (3 / 10 ^ 9) 1 = true := by decide +kernel
theorem e2 : rowOK3 0 cqE (3 / 10 ^ 9) 2 = true := by decide +kernel
theorem e3 : rowOK3 0 cqE (3 / 10 ^ 9) 3 = true := by decide +kernel
theorem e4 : rowOK3 0 cqE (3 / 10 ^ 9) 4 = true := by decide +kernel
theorem e5 : rowOK3 0 cqE (3 / 10 ^ 9) 5 = true := by decide +kernel
theorem e6 : rowOK3 0 cqE (3 / 10 ^ 9) 6 = true := by decide +kernel
theorem e7 : rowOK3 0 cqE (3 / 10 ^ 9) 7 = true := by decide +kernel

end V3Fin
