/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1272–1275 of 1732

File 319 of 430: the parts `rows22310R_1272` … `rows22310R_1275` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28864 tests: row 154 columns 0–58, row 154 columns 59–64, row 154 columns
65–68, row 154 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1272 : rowsJ2 154 155 0 59 ≤ 160707916747251 := by decide +kernel

theorem rows22310R_1273 : rowsJ2 154 155 59 65 ≤ 16098248153462 := by decide +kernel

theorem rows22310R_1274 : rowsJ2 154 155 65 69 ≤ 18614542127022 := by decide +kernel

theorem rows22310R_1275 : rowsJ2 154 155 69 72 ≤ 17320007940824 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1272
#print axioms SieveCert.rows22310R_1275
