/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 31–35 of 1732

File 8 of 430: the parts `rows22310R_31` … `rows22310R_35` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 25741 tests: row 44 columns 35–43, row 44 columns 44–399, row 45 columns
0–34, row 45 columns 35–43, row 45 columns 44–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_31 : rowsJ2 44 45 35 44 ≤ 774556769346275 := by decide +kernel

theorem rows22310R_32 : rowsJ2 44 45 44 400 ≤ 78217457712633 := by decide +kernel

theorem rows22310R_33 : rowsJ2 45 46 0 35 ≤ 1407330884584043 := by decide +kernel

theorem rows22310R_34 : rowsJ2 45 46 35 44 ≤ 754164049092089 := by decide +kernel

theorem rows22310R_35 : rowsJ2 45 46 44 400 ≤ 146953626672230 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_31
#print axioms SieveCert.rows22310R_35
