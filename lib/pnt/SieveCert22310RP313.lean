/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1248–1251 of 1732

File 313 of 430: the parts `rows22310R_1248` … `rows22310R_1251` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27588 tests: row 152 columns 0–58, row 152 columns 59–64, row 152 columns
65–68, row 152 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1248 : rowsJ2 152 153 0 59 ≤ 175437023008838 := by decide +kernel

theorem rows22310R_1249 : rowsJ2 152 153 59 65 ≤ 13574479923083 := by decide +kernel

theorem rows22310R_1250 : rowsJ2 152 153 65 69 ≤ 16317522017670 := by decide +kernel

theorem rows22310R_1251 : rowsJ2 152 153 69 72 ≤ 15268289248072 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1248
#print axioms SieveCert.rows22310R_1251
