/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1315–1318 of 1732

File 330 of 430: the parts `rows22310R_1315` … `rows22310R_1318` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25946 tests: row 157 columns 96–399, row 158 columns 0–57, row 158 columns
58–63, row 158 columns 64–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1315 : rowsJ2 157 158 96 400 ≤ 0 := by decide +kernel

theorem rows22310R_1316 : rowsJ2 158 159 0 58 ≤ 132822881849093 := by decide +kernel

theorem rows22310R_1317 : rowsJ2 158 159 58 64 ≤ 19377668312324 := by decide +kernel

theorem rows22310R_1318 : rowsJ2 158 159 64 68 ≤ 21982482949479 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1315
#print axioms SieveCert.rows22310R_1318
