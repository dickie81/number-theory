/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1054–1056 of 1732

File 264 of 430: the parts `rows22310R_1054` … `rows22310R_1056` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23063 tests: row 137 columns 79–81, row 137 columns 82–84, row 137 columns
85–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1054 : rowsJ2 137 138 79 82 ≤ 0 := by decide +kernel

theorem rows22310R_1055 : rowsJ2 137 138 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_1056 : rowsJ2 137 138 85 88 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1054
#print axioms SieveCert.rows22310R_1056
