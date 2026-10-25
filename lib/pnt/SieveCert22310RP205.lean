/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 818–821 of 1732

File 205 of 430: the parts `rows22310R_818` … `rows22310R_821` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27156 tests: row 122 columns 112–115, row 122 columns 116–399, row 123
columns 0–34, row 123 columns 35–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_818 : rowsJ2 122 123 112 116 ≤ 21669678962185 := by decide +kernel

theorem rows22310R_819 : rowsJ2 122 123 116 400 ≤ 410375976135788 := by decide +kernel

theorem rows22310R_820 : rowsJ2 123 124 0 35 ≤ 107154921209390 := by decide +kernel

theorem rows22310R_821 : rowsJ2 123 124 35 54 ≤ 335340233907587 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_818
#print axioms SieveCert.rows22310R_821
