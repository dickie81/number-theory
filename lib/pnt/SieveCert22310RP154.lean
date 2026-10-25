/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 610–613 of 1732

File 154 of 430: the parts `rows22310R_610` … `rows22310R_613` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28700 tests: row 111 columns 107–109, row 111 columns 110–399, row 112
columns 0–34, row 112 columns 35–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_610 : rowsJ2 111 112 107 110 ≤ 4641603509967 := by decide +kernel

theorem rows22310R_611 : rowsJ2 111 112 110 400 ≤ 4332788416897 := by decide +kernel

theorem rows22310R_612 : rowsJ2 112 113 0 35 ≤ 106671382669175 := by decide +kernel

theorem rows22310R_613 : rowsJ2 112 113 35 45 ≤ 224647957506457 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_610
#print axioms SieveCert.rows22310R_613
