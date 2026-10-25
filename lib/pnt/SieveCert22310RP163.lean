/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 647–649 of 1732

File 163 of 430: the parts `rows22310R_647` … `rows22310R_649` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22492 tests: row 113 columns 111–399, row 114 columns 0–34, row 114 columns
35–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_647 : rowsJ2 113 114 111 400 ≤ 8500496603193 := by decide +kernel

theorem rows22310R_648 : rowsJ2 114 115 0 35 ≤ 97849413117598 := by decide +kernel

theorem rows22310R_649 : rowsJ2 114 115 35 45 ≤ 232081731531595 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_647
#print axioms SieveCert.rows22310R_649
