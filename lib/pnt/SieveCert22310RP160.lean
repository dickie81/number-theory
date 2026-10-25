/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 635–638 of 1732

File 160 of 430: the parts `rows22310R_635` … `rows22310R_638` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25560 tests: row 113 columns 83–85, row 113 columns 86–88, row 113 columns
89–90, row 113 columns 91–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_635 : rowsJ2 113 114 83 86 ≤ 30647515675 := by decide +kernel

theorem rows22310R_636 : rowsJ2 113 114 86 89 ≤ 600755244535 := by decide +kernel

theorem rows22310R_637 : rowsJ2 113 114 89 91 ≤ 1159708870111 := by decide +kernel

theorem rows22310R_638 : rowsJ2 113 114 91 93 ≤ 2069185776067 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_635
#print axioms SieveCert.rows22310R_638
