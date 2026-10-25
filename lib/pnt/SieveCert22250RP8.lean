/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 114–130 of 5796

File 8 of 465: the parts `rows22250R_114` … `rows22250R_130` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 97857 tests: row 29 columns 29–359, row 30 columns 0–13, row 30 columns
14–16, row 30 columns 17–18, row 30 columns 19–19, row 30 columns 20–20, row 30 columns 21–21, row 30 columns 22–22,
row 30 columns 23–23, row 30 columns 24–24, row 30 columns 25–25, row 30 columns 26–26, row 30 columns 27–27, row 30
columns 28–28, row 30 columns 29–29, row 30 columns 30–359, row 31 columns 0–13), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_114 : rowsJ2 29 30 29 360 ≤ 1172605271532 := by decide +kernel

theorem rows22250R_115 : rowsJ2 30 31 0 14 ≤ 601993031975 := by decide +kernel

theorem rows22250R_116 : rowsJ2 30 31 14 17 ≤ 874382279117 := by decide +kernel

theorem rows22250R_117 : rowsJ2 30 31 17 19 ≤ 1434584101847 := by decide +kernel

theorem rows22250R_118 : rowsJ2 30 31 19 20 ≤ 960472833810 := by decide +kernel

theorem rows22250R_119 : rowsJ2 30 31 20 21 ≤ 1097034601266 := by decide +kernel

theorem rows22250R_120 : rowsJ2 30 31 21 22 ≤ 1198084988515 := by decide +kernel

theorem rows22250R_121 : rowsJ2 30 31 22 23 ≤ 1260128817268 := by decide +kernel

theorem rows22250R_122 : rowsJ2 30 31 23 24 ≤ 1283770363790 := by decide +kernel

theorem rows22250R_123 : rowsJ2 30 31 24 25 ≤ 1298981647226 := by decide +kernel

theorem rows22250R_124 : rowsJ2 30 31 25 26 ≤ 1293239502844 := by decide +kernel

theorem rows22250R_125 : rowsJ2 30 31 26 27 ≤ 1267220751245 := by decide +kernel

theorem rows22250R_126 : rowsJ2 30 31 27 28 ≤ 1216412491668 := by decide +kernel

theorem rows22250R_127 : rowsJ2 30 31 28 29 ≤ 1160758006252 := by decide +kernel

theorem rows22250R_128 : rowsJ2 30 31 29 30 ≤ 1096071672805 := by decide +kernel

theorem rows22250R_129 : rowsJ2 30 31 30 360 ≤ 1028140807821 := by decide +kernel

theorem rows22250R_130 : rowsJ2 31 32 0 14 ≤ 530044300809 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_114
#print axioms SieveCert.rows22250R_130
