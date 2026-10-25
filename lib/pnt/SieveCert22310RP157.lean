/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 622–626 of 1732

File 157 of 430: the parts `rows22310R_622` … `rows22310R_626` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29440 tests: row 112 columns 96–97, row 112 columns 98–99, row 112 columns
100–101, row 112 columns 102–103, row 112 columns 104–105), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_622 : rowsJ2 112 113 96 98 ≤ 2303340841129 := by decide +kernel

theorem rows22310R_623 : rowsJ2 112 113 98 100 ≤ 1971695895537 := by decide +kernel

theorem rows22310R_624 : rowsJ2 112 113 100 102 ≤ 1701603763533 := by decide +kernel

theorem rows22310R_625 : rowsJ2 112 113 102 104 ≤ 1675489331136 := by decide +kernel

theorem rows22310R_626 : rowsJ2 112 113 104 106 ≤ 1923917714489 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_622
#print axioms SieveCert.rows22310R_626
