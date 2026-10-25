/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 851–854 of 1732

File 213 of 430: the parts `rows22310R_851` … `rows22310R_854` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27209 tests: row 124 columns 101–103, row 124 columns 104–106, row 124
columns 107–109, row 124 columns 110–113), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_851 : rowsJ2 124 125 101 104 ≤ 1247436870452 := by decide +kernel

theorem rows22310R_852 : rowsJ2 124 125 104 107 ≤ 3908092301412 := by decide +kernel

theorem rows22310R_853 : rowsJ2 124 125 107 110 ≤ 7683528703652 := by decide +kernel

theorem rows22310R_854 : rowsJ2 124 125 110 114 ≤ 18168880936747 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_851
#print axioms SieveCert.rows22310R_854
