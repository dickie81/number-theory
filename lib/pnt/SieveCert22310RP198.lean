/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 790–793 of 1732

File 198 of 430: the parts `rows22310R_790` … `rows22310R_793` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23184 tests: row 121 columns 89–90, row 121 columns 91–92, row 121 columns
93–94, row 121 columns 95–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_790 : rowsJ2 121 122 89 91 ≤ 658474703937 := by decide +kernel

theorem rows22310R_791 : rowsJ2 121 122 91 93 ≤ 486243730156 := by decide +kernel

theorem rows22310R_792 : rowsJ2 121 122 93 95 ≤ 336087696695 := by decide +kernel

theorem rows22310R_793 : rowsJ2 121 122 95 97 ≤ 211802950561 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_790
#print axioms SieveCert.rows22310R_793
