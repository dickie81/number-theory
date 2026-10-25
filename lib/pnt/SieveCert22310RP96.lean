/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 383–386 of 1732

File 96 of 430: the parts `rows22310R_383` … `rows22310R_386` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29645 tests: row 95 columns 67–83, row 95 columns 84–88, row 95 columns
89–92, row 95 columns 93–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_383 : rowsJ2 95 96 67 84 ≤ 239561813829206 := by decide +kernel

theorem rows22310R_384 : rowsJ2 95 96 84 89 ≤ 31605489142963 := by decide +kernel

theorem rows22310R_385 : rowsJ2 95 96 89 93 ≤ 17804648201272 := by decide +kernel

theorem rows22310R_386 : rowsJ2 95 96 93 400 ≤ 11491757920646 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_383
#print axioms SieveCert.rows22310R_386
