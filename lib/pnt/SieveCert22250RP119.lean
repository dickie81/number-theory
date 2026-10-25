/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1141–1151 of 5796

File 119 of 465: the parts `rows22250R_1141` … `rows22250R_1151` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 93203 tests: row 65 columns 65–359, row 66 columns 0–17, row 66 columns
18–21, row 66 columns 22–23, row 66 columns 24–24, row 66 columns 25–25, row 66 columns 26–26, row 66 columns 27–27,
row 66 columns 28–28, row 66 columns 29–29, row 66 columns 30–30), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1141 : rowsJ2 65 66 65 360 ≤ 10671215729707 := by decide +kernel

theorem rows22250R_1142 : rowsJ2 66 67 0 18 ≤ 1690650994972 := by decide +kernel

theorem rows22250R_1143 : rowsJ2 66 67 18 22 ≤ 142198689756 := by decide +kernel

theorem rows22250R_1144 : rowsJ2 66 67 22 24 ≤ 19740885676 := by decide +kernel

theorem rows22250R_1145 : rowsJ2 66 67 24 25 ≤ 3279789057 := by decide +kernel

theorem rows22250R_1146 : rowsJ2 66 67 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1147 : rowsJ2 66 67 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1148 : rowsJ2 66 67 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1149 : rowsJ2 66 67 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1150 : rowsJ2 66 67 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1151 : rowsJ2 66 67 30 31 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1141
#print axioms SieveCert.rows22250R_1151
