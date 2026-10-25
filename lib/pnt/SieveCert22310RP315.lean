/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1256–1259 of 1732

File 315 of 430: the parts `rows22310R_1256` … `rows22310R_1259` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25774 tests: row 152 columns 85–88, row 152 columns 89–93, row 152 columns
94–99, row 152 columns 100–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1256 : rowsJ2 152 153 85 89 ≤ 3375000271046 := by decide +kernel

theorem rows22310R_1257 : rowsJ2 152 153 89 94 ≤ 1046719501536 := by decide +kernel

theorem rows22310R_1258 : rowsJ2 152 153 94 100 ≤ 0 := by decide +kernel

theorem rows22310R_1259 : rowsJ2 152 153 100 400 ≤ 61997987518396 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1256
#print axioms SieveCert.rows22310R_1259
