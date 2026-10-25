/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 136–140 of 1732

File 34 of 430: the parts `rows22310R_136` … `rows22310R_140` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29901 tests: row 66 columns 50–54, row 66 columns 55–58, row 66 columns
59–62, row 66 columns 63–65, row 66 columns 66–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_136 : rowsJ2 66 67 50 55 ≤ 111128460508319 := by decide +kernel

theorem rows22310R_137 : rowsJ2 66 67 55 59 ≤ 113110804611998 := by decide +kernel

theorem rows22310R_138 : rowsJ2 66 67 59 63 ≤ 150697974017046 := by decide +kernel

theorem rows22310R_139 : rowsJ2 66 67 63 66 ≤ 139848736078211 := by decide +kernel

theorem rows22310R_140 : rowsJ2 66 67 66 400 ≤ 45760321584015 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_136
#print axioms SieveCert.rows22310R_140
