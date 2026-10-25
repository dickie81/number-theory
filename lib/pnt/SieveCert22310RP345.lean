/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1375–1378 of 1732

File 345 of 430: the parts `rows22310R_1375` … `rows22310R_1378` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28659 tests: row 164 columns 0–55, row 164 columns 56–61, row 164 columns
62–65, row 164 columns 66–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1375 : rowsJ2 164 165 0 56 ≤ 97006930056875 := by decide +kernel

theorem rows22310R_1376 : rowsJ2 164 165 56 62 ≤ 23761511652026 := by decide +kernel

theorem rows22310R_1377 : rowsJ2 164 165 62 66 ≤ 26323394558399 := by decide +kernel

theorem rows22310R_1378 : rowsJ2 164 165 66 69 ≤ 24405521331291 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1375
#print axioms SieveCert.rows22310R_1378
