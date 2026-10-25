/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 496–500 of 5796

File 51 of 465: the parts `rows22250R_496` … `rows22250R_500` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 82489 tests: row 48 columns 32–32, row 48 columns 33–33, row 48 columns
34–34, row 48 columns 35–35, row 48 columns 36–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_496 : rowsJ2 48 49 32 33 ≤ 171162401160 := by decide +kernel

theorem rows22250R_497 : rowsJ2 48 49 33 34 ≤ 152110438319 := by decide +kernel

theorem rows22250R_498 : rowsJ2 48 49 34 35 ≤ 135114979047 := by decide +kernel

theorem rows22250R_499 : rowsJ2 48 49 35 36 ≤ 111450203560 := by decide +kernel

theorem rows22250R_500 : rowsJ2 48 49 36 37 ≤ 93543820529 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_496
#print axioms SieveCert.rows22250R_500
