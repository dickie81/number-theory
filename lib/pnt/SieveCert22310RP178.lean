/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 707–710 of 1732

File 178 of 430: the parts `rows22310R_707` … `rows22310R_710` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28340 tests: row 117 columns 46–72, row 117 columns 73–78, row 117 columns
79–82, row 117 columns 83–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_707 : rowsJ2 117 118 46 73 ≤ 279832800564755 := by decide +kernel

theorem rows22310R_708 : rowsJ2 117 118 73 79 ≤ 3445814213316 := by decide +kernel

theorem rows22310R_709 : rowsJ2 117 118 79 83 ≤ 0 := by decide +kernel

theorem rows22310R_710 : rowsJ2 117 118 83 86 ≤ 29960283468 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_707
#print axioms SieveCert.rows22310R_710
