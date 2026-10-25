/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 986–989 of 1732

File 247 of 430: the parts `rows22310R_986` … `rows22310R_989` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27988 tests: row 132 columns 102–105, row 132 columns 106–109, row 132
columns 110–399, row 133 columns 0–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_986 : rowsJ2 132 133 102 106 ≤ 5212957356117 := by decide +kernel

theorem rows22310R_987 : rowsJ2 132 133 106 110 ≤ 13869703396100 := by decide +kernel

theorem rows22310R_988 : rowsJ2 132 133 110 400 ≤ 746171955826169 := by decide +kernel

theorem rows22310R_989 : rowsJ2 133 134 0 37 ≤ 201682555917188 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_986
#print axioms SieveCert.rows22310R_989
