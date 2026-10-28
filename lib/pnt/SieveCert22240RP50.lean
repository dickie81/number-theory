/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 502–507 of 5066

File 50 of 387: the parts `rows22240R_502` … `rows22240R_507` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 90368 in units of a depth-4 test: row 48 columns 32–32, row 48 columns
33–33, row 48 columns 34–34, row 48 columns 35–35, row 48 columns 36–36, row 48 columns 37–37), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_502 : rowsJ2 48 49 32 33 ≤ 190091793213 := by decide +kernel

theorem rows22240R_503 : rowsJ2 48 49 33 34 ≤ 159853430767 := by decide +kernel

theorem rows22240R_504 : rowsJ2 48 49 34 35 ≤ 136785127726 := by decide +kernel

theorem rows22240R_505 : rowsJ2 48 49 35 36 ≤ 110110519696 := by decide +kernel

theorem rows22240R_506 : rowsJ2 48 49 36 37 ≤ 89678752516 := by decide +kernel

theorem rows22240R_507 : rowsJ2 48 49 37 38 ≤ 68078837774 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_502
#print axioms SieveCert.rows22240R_507
