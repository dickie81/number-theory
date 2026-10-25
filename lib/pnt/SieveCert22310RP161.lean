/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 639–642 of 1732

File 161 of 430: the parts `rows22310R_639` … `rows22310R_642` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24656 tests: row 113 columns 93–94, row 113 columns 95–96, row 113 columns
97–98, row 113 columns 99–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_639 : rowsJ2 113 114 93 95 ≤ 2437428775239 := by decide +kernel

theorem rows22310R_640 : rowsJ2 113 114 95 97 ≤ 2101110821951 := by decide +kernel

theorem rows22310R_641 : rowsJ2 113 114 97 99 ≤ 1785145046194 := by decide +kernel

theorem rows22310R_642 : rowsJ2 113 114 99 101 ≤ 1490727702810 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_639
#print axioms SieveCert.rows22310R_642
