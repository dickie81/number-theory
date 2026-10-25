/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1193–1205 of 5796

File 124 of 465: the parts `rows22250R_1193` … `rows22250R_1205` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99928 tests: row 67 columns 26–26, row 67 columns 27–27, row 67 columns
28–28, row 67 columns 29–29, row 67 columns 30–30, row 67 columns 31–31, row 67 columns 32–32, row 67 columns 33–33,
row 67 columns 34–34, row 67 columns 35–35, row 67 columns 36–36, row 67 columns 37–37, row 67 columns 38–38), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1193 : rowsJ2 67 68 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1194 : rowsJ2 67 68 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1195 : rowsJ2 67 68 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1196 : rowsJ2 67 68 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1197 : rowsJ2 67 68 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1198 : rowsJ2 67 68 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1199 : rowsJ2 67 68 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1200 : rowsJ2 67 68 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1201 : rowsJ2 67 68 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1202 : rowsJ2 67 68 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1203 : rowsJ2 67 68 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1204 : rowsJ2 67 68 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1205 : rowsJ2 67 68 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1193
#print axioms SieveCert.rows22250R_1205
