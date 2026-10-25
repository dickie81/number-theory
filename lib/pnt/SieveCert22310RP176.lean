/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 699–702 of 1732

File 176 of 430: the parts `rows22310R_699` … `rows22310R_702` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27577 tests: row 116 columns 101–102, row 116 columns 103–105, row 116
columns 106–108, row 116 columns 109–111), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_699 : rowsJ2 116 117 101 103 ≤ 797616920680 := by decide +kernel

theorem rows22310R_700 : rowsJ2 116 117 103 106 ≤ 2077753975899 := by decide +kernel

theorem rows22310R_701 : rowsJ2 116 117 106 109 ≤ 4035586963487 := by decide +kernel

theorem rows22310R_702 : rowsJ2 116 117 109 112 ≤ 7091494279953 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_699
#print axioms SieveCert.rows22310R_702
