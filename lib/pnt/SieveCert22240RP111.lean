/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1139–1149 of 5066

File 111 of 387: the parts `rows22240R_1139` … `rows22240R_1149` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 99141 in units of a depth-4 test: row 65 columns 45–45, row 65 columns
46–46, row 65 columns 47–47, row 65 columns 48–48, row 65 columns 49–49, row 65 columns 50–50, row 65 columns 51–51,
row 65 columns 52–52, row 65 columns 53–53, row 65 columns 54–54, row 65 columns 55–55), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1139 : rowsJ2 65 66 45 46 ≤ 195439448156 := by decide +kernel

theorem rows22240R_1140 : rowsJ2 65 66 46 47 ≤ 381134311932 := by decide +kernel

theorem rows22240R_1141 : rowsJ2 65 66 47 48 ≤ 813753457733 := by decide +kernel

theorem rows22240R_1142 : rowsJ2 65 66 48 49 ≤ 1554675781210 := by decide +kernel

theorem rows22240R_1143 : rowsJ2 65 66 49 50 ≤ 2397514092151 := by decide +kernel

theorem rows22240R_1144 : rowsJ2 65 66 50 51 ≤ 3271389897512 := by decide +kernel

theorem rows22240R_1145 : rowsJ2 65 66 51 52 ≤ 4304329662091 := by decide +kernel

theorem rows22240R_1146 : rowsJ2 65 66 52 53 ≤ 5578301396132 := by decide +kernel

theorem rows22240R_1147 : rowsJ2 65 66 53 54 ≤ 6679537848794 := by decide +kernel

theorem rows22240R_1148 : rowsJ2 65 66 54 55 ≤ 7558507504667 := by decide +kernel

theorem rows22240R_1149 : rowsJ2 65 66 55 56 ≤ 8395895547678 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1139
#print axioms SieveCert.rows22240R_1149
