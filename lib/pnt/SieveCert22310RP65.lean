/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 261–264 of 1732

File 65 of 430: the parts `rows22310R_261` … `rows22310R_264` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23396 tests: row 80 columns 79–399, row 81 columns 0–34, row 81 columns
35–43, row 81 columns 44–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_261 : rowsJ2 80 81 79 400 ≤ 44794660785931 := by decide +kernel

theorem rows22310R_262 : rowsJ2 81 82 0 35 ≤ 687885640391832 := by decide +kernel

theorem rows22310R_263 : rowsJ2 81 82 35 44 ≤ 94944663048665 := by decide +kernel

theorem rows22310R_264 : rowsJ2 81 82 44 50 ≤ 82166259492808 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_261
#print axioms SieveCert.rows22310R_264
