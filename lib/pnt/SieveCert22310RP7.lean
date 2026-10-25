/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 28–30 of 1732

File 7 of 430: the parts `rows22310R_28` … `rows22310R_30` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22950 tests: row 43 columns 0–34, row 43 columns 35–399, row 44 columns
0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_28 : rowsJ2 43 44 0 35 ≤ 1437794472420875 := by decide +kernel

theorem rows22310R_29 : rowsJ2 43 44 35 400 ≤ 794564465515296 := by decide +kernel

theorem rows22310R_30 : rowsJ2 44 45 0 35 ≤ 1422521580830452 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_28
#print axioms SieveCert.rows22310R_30
