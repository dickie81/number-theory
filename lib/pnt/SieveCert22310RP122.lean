/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 484–486 of 1732

File 122 of 430: the parts `rows22310R_484` … `rows22310R_486` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22394 tests: row 104 columns 44–51, row 104 columns 52–65, row 104 columns
66–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_484 : rowsJ2 104 105 44 52 ≤ 240811370869193 := by decide +kernel

theorem rows22310R_485 : rowsJ2 104 105 52 66 ≤ 286851514351629 := by decide +kernel

theorem rows22310R_486 : rowsJ2 104 105 66 82 ≤ 139223252062126 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_484
#print axioms SieveCert.rows22310R_486
