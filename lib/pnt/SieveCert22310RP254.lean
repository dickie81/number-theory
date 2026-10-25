/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1014–1017 of 1732

File 254 of 430: the parts `rows22310R_1014` … `rows22310R_1017` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27048 tests: row 134 columns 94–96, row 134 columns 97–99, row 134 columns
100–103, row 134 columns 104–107), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1014 : rowsJ2 134 135 94 97 ≤ 0 := by decide +kernel

theorem rows22310R_1015 : rowsJ2 134 135 97 100 ≤ 0 := by decide +kernel

theorem rows22310R_1016 : rowsJ2 134 135 100 104 ≤ 2260517958495 := by decide +kernel

theorem rows22310R_1017 : rowsJ2 134 135 104 108 ≤ 10058094028056 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1014
#print axioms SieveCert.rows22310R_1017
