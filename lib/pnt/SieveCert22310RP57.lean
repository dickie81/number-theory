/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 229–232 of 1732

File 57 of 430: the parts `rows22310R_229` … `rows22310R_232` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27780 tests: row 77 columns 50–54, row 77 columns 55–58, row 77 columns
59–62, row 77 columns 63–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_229 : rowsJ2 77 78 50 55 ≤ 114099739031709 := by decide +kernel

theorem rows22310R_230 : rowsJ2 77 78 55 59 ≤ 144255588650372 := by decide +kernel

theorem rows22310R_231 : rowsJ2 77 78 59 63 ≤ 165043545026797 := by decide +kernel

theorem rows22310R_232 : rowsJ2 77 78 63 68 ≤ 187592617989740 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_229
#print axioms SieveCert.rows22310R_232
