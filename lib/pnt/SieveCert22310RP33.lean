/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 132–135 of 1732

File 33 of 430: the parts `rows22310R_132` … `rows22310R_135` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28470 tests: row 65 columns 63–399, row 66 columns 0–34, row 66 columns
35–43, row 66 columns 44–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_132 : rowsJ2 65 66 63 400 ≤ 139156708127059 := by decide +kernel

theorem rows22310R_133 : rowsJ2 66 67 0 35 ≤ 1048366893489177 := by decide +kernel

theorem rows22310R_134 : rowsJ2 66 67 35 44 ≤ 299401209187905 := by decide +kernel

theorem rows22310R_135 : rowsJ2 66 67 44 50 ≤ 131449659203075 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_132
#print axioms SieveCert.rows22310R_135
