import CmLhD

/-! # Kernel check that the piecewise coefficients `Lh p` equal the data `LD p` (pieces 0–31) -/

namespace CmLhChk

open CmW CmLhD

theorem c0 : decide (Lh 0 = LD 0) = true := by decide +kernel
theorem c1 : decide (Lh 1 = LD 1) = true := by decide +kernel
theorem c2 : decide (Lh 2 = LD 2) = true := by decide +kernel
theorem c3 : decide (Lh 3 = LD 3) = true := by decide +kernel
theorem c4 : decide (Lh 4 = LD 4) = true := by decide +kernel
theorem c5 : decide (Lh 5 = LD 5) = true := by decide +kernel
theorem c6 : decide (Lh 6 = LD 6) = true := by decide +kernel
theorem c7 : decide (Lh 7 = LD 7) = true := by decide +kernel
theorem c8 : decide (Lh 8 = LD 8) = true := by decide +kernel
theorem c9 : decide (Lh 9 = LD 9) = true := by decide +kernel
theorem c10 : decide (Lh 10 = LD 10) = true := by decide +kernel
theorem c11 : decide (Lh 11 = LD 11) = true := by decide +kernel
theorem c12 : decide (Lh 12 = LD 12) = true := by decide +kernel
theorem c13 : decide (Lh 13 = LD 13) = true := by decide +kernel
theorem c14 : decide (Lh 14 = LD 14) = true := by decide +kernel
theorem c15 : decide (Lh 15 = LD 15) = true := by decide +kernel
theorem c16 : decide (Lh 16 = LD 16) = true := by decide +kernel
theorem c17 : decide (Lh 17 = LD 17) = true := by decide +kernel
theorem c18 : decide (Lh 18 = LD 18) = true := by decide +kernel
theorem c19 : decide (Lh 19 = LD 19) = true := by decide +kernel
theorem c20 : decide (Lh 20 = LD 20) = true := by decide +kernel
theorem c21 : decide (Lh 21 = LD 21) = true := by decide +kernel
theorem c22 : decide (Lh 22 = LD 22) = true := by decide +kernel
theorem c23 : decide (Lh 23 = LD 23) = true := by decide +kernel
theorem c24 : decide (Lh 24 = LD 24) = true := by decide +kernel
theorem c25 : decide (Lh 25 = LD 25) = true := by decide +kernel
theorem c26 : decide (Lh 26 = LD 26) = true := by decide +kernel
theorem c27 : decide (Lh 27 = LD 27) = true := by decide +kernel
theorem c28 : decide (Lh 28 = LD 28) = true := by decide +kernel
theorem c29 : decide (Lh 29 = LD 29) = true := by decide +kernel
theorem c30 : decide (Lh 30 = LD 30) = true := by decide +kernel
theorem c31 : decide (Lh 31 = LD 31) = true := by decide +kernel

end CmLhChk
