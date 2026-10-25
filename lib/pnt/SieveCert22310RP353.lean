/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1405–1408 of 1732

File 353 of 430: the parts `rows22310R_1405` … `rows22310R_1408` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29741 tests: row 167 columns 65–68, row 167 columns 69–72, row 167 columns
73–77, row 167 columns 78–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1405 : rowsJ2 167 168 65 69 ≤ 32470719348749 := by decide +kernel

theorem rows22310R_1406 : rowsJ2 167 168 69 73 ≤ 22148908582525 := by decide +kernel

theorem rows22310R_1407 : rowsJ2 167 168 73 78 ≤ 15733253418888 := by decide +kernel

theorem rows22310R_1408 : rowsJ2 167 168 78 83 ≤ 6518199983979 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1405
#print axioms SieveCert.rows22310R_1408
