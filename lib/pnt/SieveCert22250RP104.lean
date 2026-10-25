/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1140–1156 of 4715

File 104 of 351: the parts `rows22250R_1140` … `rows22250R_1156` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98648 tests: row 66 columns 25–25, row 66 columns 26–26, row 66 columns
27–27, row 66 columns 28–28, row 66 columns 29–29, row 66 columns 30–30, row 66 columns 31–31, row 66 columns 32–32,
row 66 columns 33–33, row 66 columns 34–34, row 66 columns 35–35, row 66 columns 36–37, row 66 columns 38–39, row 66
columns 40–41, row 66 columns 42–42, row 66 columns 43–43, row 66 columns 44–44), each a sum of refined costs
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

theorem rows22250R_1140 : rowsJ2 66 67 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1141 : rowsJ2 66 67 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1142 : rowsJ2 66 67 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1143 : rowsJ2 66 67 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1144 : rowsJ2 66 67 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1145 : rowsJ2 66 67 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1146 : rowsJ2 66 67 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1147 : rowsJ2 66 67 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1148 : rowsJ2 66 67 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1149 : rowsJ2 66 67 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1150 : rowsJ2 66 67 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1151 : rowsJ2 66 67 36 38 ≤ 0 := by decide +kernel

theorem rows22250R_1152 : rowsJ2 66 67 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1153 : rowsJ2 66 67 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1154 : rowsJ2 66 67 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1155 : rowsJ2 66 67 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1156 : rowsJ2 66 67 44 45 ≤ 65277868781 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1140
#print axioms SieveCert.rows22250R_1156
