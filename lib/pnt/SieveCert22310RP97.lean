/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 387–390 of 1732

File 97 of 430: the parts `rows22310R_387` … `rows22310R_390` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29681 tests: row 96 columns 0–34, row 96 columns 35–43, row 96 columns 44–49,
row 96 columns 50–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_387 : rowsJ2 96 97 0 35 ≤ 322085969242729 := by decide +kernel

theorem rows22310R_388 : rowsJ2 96 97 35 44 ≤ 72504563544465 := by decide +kernel

theorem rows22310R_389 : rowsJ2 96 97 44 50 ≤ 163962615176177 := by decide +kernel

theorem rows22310R_390 : rowsJ2 96 97 50 57 ≤ 226455638472236 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_387
#print axioms SieveCert.rows22310R_390
