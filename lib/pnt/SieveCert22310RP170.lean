/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 675–678 of 1732

File 170 of 430: the parts `rows22310R_675` … `rows22310R_678` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24563 tests: row 115 columns 91–92, row 115 columns 93–94, row 115 columns
95–96, row 115 columns 97–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_675 : rowsJ2 115 116 91 93 ≤ 1870554305812 := by decide +kernel

theorem rows22310R_676 : rowsJ2 115 116 93 95 ≤ 1729112693895 := by decide +kernel

theorem rows22310R_677 : rowsJ2 115 116 95 97 ≤ 1444110843068 := by decide +kernel

theorem rows22310R_678 : rowsJ2 115 116 97 99 ≤ 1181002303152 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_675
#print axioms SieveCert.rows22310R_678
