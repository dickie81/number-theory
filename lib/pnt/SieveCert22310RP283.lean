/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1129–1131 of 1732

File 283 of 430: the parts `rows22310R_1129` … `rows22310R_1131` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23023 tests: row 142 columns 90–93, row 142 columns 94–97, row 142 columns
98–102), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1129 : rowsJ2 142 143 90 94 ≤ 0 := by decide +kernel

theorem rows22310R_1130 : rowsJ2 142 143 94 98 ≤ 0 := by decide +kernel

theorem rows22310R_1131 : rowsJ2 142 143 98 103 ≤ 1606207368606 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1129
#print axioms SieveCert.rows22310R_1131
