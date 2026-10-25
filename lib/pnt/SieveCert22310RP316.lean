/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1260–1263 of 1732

File 316 of 430: the parts `rows22310R_1260` … `rows22310R_1263` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28226 tests: row 153 columns 0–58, row 153 columns 59–64, row 153 columns
65–68, row 153 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1260 : rowsJ2 153 154 0 59 ≤ 167524179510931 := by decide +kernel

theorem rows22310R_1261 : rowsJ2 153 154 59 65 ≤ 14829541474838 := by decide +kernel

theorem rows22310R_1262 : rowsJ2 153 154 65 69 ≤ 17459337369317 := by decide +kernel

theorem rows22310R_1263 : rowsJ2 153 154 69 72 ≤ 16287922960740 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1260
#print axioms SieveCert.rows22310R_1263
