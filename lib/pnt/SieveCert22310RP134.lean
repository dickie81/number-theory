/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 530–533 of 1732

File 134 of 430: the parts `rows22310R_530` … `rows22310R_533` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29156 tests: row 107 columns 53–74, row 107 columns 75–82, row 107 columns
83–86, row 107 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_530 : rowsJ2 107 108 53 75 ≤ 309578468128067 := by decide +kernel

theorem rows22310R_531 : rowsJ2 107 108 75 83 ≤ 28993105363768 := by decide +kernel

theorem rows22310R_532 : rowsJ2 107 108 83 87 ≤ 3421507384988 := by decide +kernel

theorem rows22310R_533 : rowsJ2 107 108 87 90 ≤ 1133770444854 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_530
#print axioms SieveCert.rows22310R_533
