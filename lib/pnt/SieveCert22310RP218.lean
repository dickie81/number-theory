/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 871–873 of 1732

File 218 of 430: the parts `rows22310R_871` … `rows22310R_873` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23334 tests: row 125 columns 108–111, row 125 columns 112–399, row 126
columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_871 : rowsJ2 125 126 108 112 ≤ 14048846022908 := by decide +kernel

theorem rows22310R_872 : rowsJ2 125 126 112 400 ≤ 759100302393242 := by decide +kernel

theorem rows22310R_873 : rowsJ2 126 127 0 35 ≤ 127430356149212 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_871
#print axioms SieveCert.rows22310R_873
