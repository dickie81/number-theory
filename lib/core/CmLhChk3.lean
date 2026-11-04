import CmLhChk2

/-! # Kernel check that the piecewise coefficients `Lh p` equal the data `LD p` (pieces 96–127) -/

namespace CmLhChk

open CmW CmLhD

theorem c96 : decide (Lh 96 = LD 96) = true := by decide +kernel
theorem c97 : decide (Lh 97 = LD 97) = true := by decide +kernel
theorem c98 : decide (Lh 98 = LD 98) = true := by decide +kernel
theorem c99 : decide (Lh 99 = LD 99) = true := by decide +kernel
theorem c100 : decide (Lh 100 = LD 100) = true := by decide +kernel
theorem c101 : decide (Lh 101 = LD 101) = true := by decide +kernel
theorem c102 : decide (Lh 102 = LD 102) = true := by decide +kernel
theorem c103 : decide (Lh 103 = LD 103) = true := by decide +kernel
theorem c104 : decide (Lh 104 = LD 104) = true := by decide +kernel
theorem c105 : decide (Lh 105 = LD 105) = true := by decide +kernel
theorem c106 : decide (Lh 106 = LD 106) = true := by decide +kernel
theorem c107 : decide (Lh 107 = LD 107) = true := by decide +kernel
theorem c108 : decide (Lh 108 = LD 108) = true := by decide +kernel
theorem c109 : decide (Lh 109 = LD 109) = true := by decide +kernel
theorem c110 : decide (Lh 110 = LD 110) = true := by decide +kernel
theorem c111 : decide (Lh 111 = LD 111) = true := by decide +kernel
theorem c112 : decide (Lh 112 = LD 112) = true := by decide +kernel
theorem c113 : decide (Lh 113 = LD 113) = true := by decide +kernel
theorem c114 : decide (Lh 114 = LD 114) = true := by decide +kernel
theorem c115 : decide (Lh 115 = LD 115) = true := by decide +kernel
theorem c116 : decide (Lh 116 = LD 116) = true := by decide +kernel
theorem c117 : decide (Lh 117 = LD 117) = true := by decide +kernel
theorem c118 : decide (Lh 118 = LD 118) = true := by decide +kernel
theorem c119 : decide (Lh 119 = LD 119) = true := by decide +kernel
theorem c120 : decide (Lh 120 = LD 120) = true := by decide +kernel
theorem c121 : decide (Lh 121 = LD 121) = true := by decide +kernel
theorem c122 : decide (Lh 122 = LD 122) = true := by decide +kernel
theorem c123 : decide (Lh 123 = LD 123) = true := by decide +kernel
theorem c124 : decide (Lh 124 = LD 124) = true := by decide +kernel
theorem c125 : decide (Lh 125 = LD 125) = true := by decide +kernel
theorem c126 : decide (Lh 126 = LD 126) = true := by decide +kernel
theorem c127 : decide (Lh 127 = LD 127) = true := by decide +kernel

end CmLhChk

namespace CmLhChk
open CmW CmLhD

theorem Lh_eq (p : ℕ) (hp : p < CmW.NP) : Lh p = LD p := by
  have : p < 128 := hp
  interval_cases p
  exacts [of_decide_eq_true c0, of_decide_eq_true c1, of_decide_eq_true c2, of_decide_eq_true c3, of_decide_eq_true c4, of_decide_eq_true c5, of_decide_eq_true c6, of_decide_eq_true c7, of_decide_eq_true c8, of_decide_eq_true c9, of_decide_eq_true c10, of_decide_eq_true c11, of_decide_eq_true c12, of_decide_eq_true c13, of_decide_eq_true c14, of_decide_eq_true c15, of_decide_eq_true c16, of_decide_eq_true c17, of_decide_eq_true c18, of_decide_eq_true c19, of_decide_eq_true c20, of_decide_eq_true c21, of_decide_eq_true c22, of_decide_eq_true c23, of_decide_eq_true c24, of_decide_eq_true c25, of_decide_eq_true c26, of_decide_eq_true c27, of_decide_eq_true c28, of_decide_eq_true c29, of_decide_eq_true c30, of_decide_eq_true c31, of_decide_eq_true c32, of_decide_eq_true c33, of_decide_eq_true c34, of_decide_eq_true c35, of_decide_eq_true c36, of_decide_eq_true c37, of_decide_eq_true c38, of_decide_eq_true c39, of_decide_eq_true c40, of_decide_eq_true c41, of_decide_eq_true c42, of_decide_eq_true c43, of_decide_eq_true c44, of_decide_eq_true c45, of_decide_eq_true c46, of_decide_eq_true c47, of_decide_eq_true c48, of_decide_eq_true c49, of_decide_eq_true c50, of_decide_eq_true c51, of_decide_eq_true c52, of_decide_eq_true c53, of_decide_eq_true c54, of_decide_eq_true c55, of_decide_eq_true c56, of_decide_eq_true c57, of_decide_eq_true c58, of_decide_eq_true c59, of_decide_eq_true c60, of_decide_eq_true c61, of_decide_eq_true c62, of_decide_eq_true c63, of_decide_eq_true c64, of_decide_eq_true c65, of_decide_eq_true c66, of_decide_eq_true c67, of_decide_eq_true c68, of_decide_eq_true c69, of_decide_eq_true c70, of_decide_eq_true c71, of_decide_eq_true c72, of_decide_eq_true c73, of_decide_eq_true c74, of_decide_eq_true c75, of_decide_eq_true c76, of_decide_eq_true c77, of_decide_eq_true c78, of_decide_eq_true c79, of_decide_eq_true c80, of_decide_eq_true c81, of_decide_eq_true c82, of_decide_eq_true c83, of_decide_eq_true c84, of_decide_eq_true c85, of_decide_eq_true c86, of_decide_eq_true c87, of_decide_eq_true c88, of_decide_eq_true c89, of_decide_eq_true c90, of_decide_eq_true c91, of_decide_eq_true c92, of_decide_eq_true c93, of_decide_eq_true c94, of_decide_eq_true c95, of_decide_eq_true c96, of_decide_eq_true c97, of_decide_eq_true c98, of_decide_eq_true c99, of_decide_eq_true c100, of_decide_eq_true c101, of_decide_eq_true c102, of_decide_eq_true c103, of_decide_eq_true c104, of_decide_eq_true c105, of_decide_eq_true c106, of_decide_eq_true c107, of_decide_eq_true c108, of_decide_eq_true c109, of_decide_eq_true c110, of_decide_eq_true c111, of_decide_eq_true c112, of_decide_eq_true c113, of_decide_eq_true c114, of_decide_eq_true c115, of_decide_eq_true c116, of_decide_eq_true c117, of_decide_eq_true c118, of_decide_eq_true c119, of_decide_eq_true c120, of_decide_eq_true c121, of_decide_eq_true c122, of_decide_eq_true c123, of_decide_eq_true c124, of_decide_eq_true c125, of_decide_eq_true c126, of_decide_eq_true c127]

end CmLhChk
