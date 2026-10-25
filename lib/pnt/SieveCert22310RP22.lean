/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 88–91 of 1732

File 22 of 430: the parts `rows22310R_88` … `rows22310R_91` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 59 columns 0–34, row 59 columns 35–43, row 59 columns 44–49,
row 59 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22310R_88 : rowsJ2 59 60 0 35 ≤ 1183504743812473 := by decide +kernel

theorem rows22310R_89 : rowsJ2 59 60 35 44 ≤ 444232964260323 := by decide +kernel

theorem rows22310R_90 : rowsJ2 59 60 44 50 ≤ 196892189451698 := by decide +kernel

theorem rows22310R_91 : rowsJ2 59 60 50 55 ≤ 140267660552145 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_88
#print axioms SieveCert.rows22310R_91
