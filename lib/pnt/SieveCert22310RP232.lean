/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 926–929 of 1732

File 232 of 430: the parts `rows22310R_926` … `rows22310R_929` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28224 tests: row 129 columns 68–73, row 129 columns 74–77, row 129 columns
78–80, row 129 columns 81–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_926 : rowsJ2 129 130 68 74 ≤ 570241882937 := by decide +kernel

theorem rows22310R_927 : rowsJ2 129 130 74 78 ≤ 0 := by decide +kernel

theorem rows22310R_928 : rowsJ2 129 130 78 81 ≤ 0 := by decide +kernel

theorem rows22310R_929 : rowsJ2 129 130 81 84 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_926
#print axioms SieveCert.rows22310R_929
