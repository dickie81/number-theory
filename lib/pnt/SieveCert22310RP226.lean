/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 902–905 of 1732

File 226 of 430: the parts `rows22310R_902` … `rows22310R_905` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27209 tests: row 127 columns 98–100, row 127 columns 101–103, row 127 columns
104–106, row 127 columns 107–110), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_902 : rowsJ2 127 128 98 101 ≤ 0 := by decide +kernel

theorem rows22310R_903 : rowsJ2 127 128 101 104 ≤ 1498510408899 := by decide +kernel

theorem rows22310R_904 : rowsJ2 127 128 104 107 ≤ 4632299234196 := by decide +kernel

theorem rows22310R_905 : rowsJ2 127 128 107 111 ≤ 13085273758331 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_902
#print axioms SieveCert.rows22310R_905
