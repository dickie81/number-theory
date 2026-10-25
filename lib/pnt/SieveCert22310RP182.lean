/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 725–727 of 1732

File 182 of 430: the parts `rows22310R_725` … `rows22310R_727` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23407 tests: row 118 columns 0–34, row 118 columns 35–46, row 118 columns
47–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_725 : rowsJ2 118 119 0 35 ≤ 92095143972856 := by decide +kernel

theorem rows22310R_726 : rowsJ2 118 119 35 47 ≤ 276197334704436 := by decide +kernel

theorem rows22310R_727 : rowsJ2 118 119 47 74 ≤ 242370632461568 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_725
#print axioms SieveCert.rows22310R_727
