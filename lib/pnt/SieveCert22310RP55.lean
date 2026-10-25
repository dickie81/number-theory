/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 221–224 of 1732

File 55 of 430: the parts `rows22310R_221` … `rows22310R_224` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28335 tests: row 76 columns 55–58, row 76 columns 59–62, row 76 columns
63–67, row 76 columns 68–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_221 : rowsJ2 76 77 55 59 ≤ 139393155428436 := by decide +kernel

theorem rows22310R_222 : rowsJ2 76 77 59 63 ≤ 168178522858887 := by decide +kernel

theorem rows22310R_223 : rowsJ2 76 77 63 68 ≤ 191657680417477 := by decide +kernel

theorem rows22310R_224 : rowsJ2 76 77 68 74 ≤ 202188591598399 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_221
#print axioms SieveCert.rows22310R_224
