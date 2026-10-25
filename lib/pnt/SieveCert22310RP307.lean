/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1223–1226 of 1732

File 307 of 430: the parts `rows22310R_1223` … `rows22310R_1226` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26374 tests: row 150 columns 0–58, row 150 columns 59–64, row 150 columns
65–68, row 150 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1223 : rowsJ2 150 151 0 59 ≤ 191310349009149 := by decide +kernel

theorem rows22310R_1224 : rowsJ2 150 151 59 65 ≤ 11299856477049 := by decide +kernel

theorem rows22310R_1225 : rowsJ2 150 151 65 69 ≤ 14197989444667 := by decide +kernel

theorem rows22310R_1226 : rowsJ2 150 151 69 72 ≤ 13356429470580 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1223
#print axioms SieveCert.rows22310R_1226
