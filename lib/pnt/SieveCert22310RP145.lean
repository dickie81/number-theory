/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 574–577 of 1732

File 145 of 430: the parts `rows22310R_574` … `rows22310R_577` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24606 tests: row 109 columns 104–105, row 109 columns 106–107, row 109
columns 108–399, row 110 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_574 : rowsJ2 109 110 104 106 ≤ 2581480429186 := by decide +kernel

theorem rows22310R_575 : rowsJ2 109 110 106 108 ≤ 2876324194974 := by decide +kernel

theorem rows22310R_576 : rowsJ2 109 110 108 400 ≤ 3449824672731 := by decide +kernel

theorem rows22310R_577 : rowsJ2 110 111 0 35 ≤ 119432219908485 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_574
#print axioms SieveCert.rows22310R_577
