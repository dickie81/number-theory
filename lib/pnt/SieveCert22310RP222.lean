/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 886–889 of 1732

File 222 of 430: the parts `rows22310R_886` … `rows22310R_889` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27973 tests: row 126 columns 102–104, row 126 columns 105–107, row 126
columns 108–111, row 126 columns 112–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_886 : rowsJ2 126 127 102 105 ≤ 2288545707348 := by decide +kernel

theorem rows22310R_887 : rowsJ2 126 127 105 108 ≤ 5638474816403 := by decide +kernel

theorem rows22310R_888 : rowsJ2 126 127 108 112 ≤ 14768459044177 := by decide +kernel

theorem rows22310R_889 : rowsJ2 126 127 112 400 ≤ 817980101325288 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_886
#print axioms SieveCert.rows22310R_889
