/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1284–1287 of 1732

File 322 of 430: the parts `rows22310R_1284` … `rows22310R_1287` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26908 tests: row 155 columns 58–63, row 155 columns 64–67, row 155 columns
68–70, row 155 columns 71–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1284 : rowsJ2 155 156 58 64 ≤ 15211569484923 := by decide +kernel

theorem rows22310R_1285 : rowsJ2 155 156 64 68 ≤ 18246356357250 := by decide +kernel

theorem rows22310R_1286 : rowsJ2 155 156 68 71 ≤ 17527589915147 := by decide +kernel

theorem rows22310R_1287 : rowsJ2 155 156 71 74 ≤ 18344796664714 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1284
#print axioms SieveCert.rows22310R_1287
