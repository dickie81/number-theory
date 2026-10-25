/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 68–71 of 1732

File 17 of 430: the parts `rows22310R_68` … `rows22310R_71` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–49,
row 55 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22310R_68 : rowsJ2 55 56 0 35 ≤ 1251525778173366 := by decide +kernel

theorem rows22310R_69 : rowsJ2 55 56 35 44 ≤ 534162887752060 := by decide +kernel

theorem rows22310R_70 : rowsJ2 55 56 44 50 ≤ 245902595880131 := by decide +kernel

theorem rows22310R_71 : rowsJ2 55 56 50 55 ≤ 167023180843487 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_68
#print axioms SieveCert.rows22310R_71
