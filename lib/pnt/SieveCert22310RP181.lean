/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 720–724 of 1732

File 181 of 430: the parts `rows22310R_720` … `rows22310R_724` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29003 tests: row 117 columns 105–107, row 117 columns 108–110, row 117
columns 111–113, row 117 columns 114–116, row 117 columns 117–399), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_720 : rowsJ2 117 118 105 108 ≤ 3339072244720 := by decide +kernel

theorem rows22310R_721 : rowsJ2 117 118 108 111 ≤ 6238605656449 := by decide +kernel

theorem rows22310R_722 : rowsJ2 117 118 111 114 ≤ 10276862011926 := by decide +kernel

theorem rows22310R_723 : rowsJ2 117 118 114 117 ≤ 15474407135426 := by decide +kernel

theorem rows22310R_724 : rowsJ2 117 118 117 400 ≤ 6514784278626 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_720
#print axioms SieveCert.rows22310R_724
