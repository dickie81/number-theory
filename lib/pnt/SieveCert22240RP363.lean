/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4662–4677 of 5066

File 363 of 387: the parts `rows22240R_4662` … `rows22240R_4677` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99839 in units of a depth-4 test: row 167 columns 0–38, row 167 columns
39–40, row 167 columns 41–42, row 167 columns 43–43, row 167 columns 44–44, row 167 columns 45–45, row 167 columns
46–46, row 167 columns 47–47, row 167 columns 48–48, row 167 columns 49–49, row 167 columns 50–50, row 167 columns
51–51, row 167 columns 52–52, row 167 columns 53–53, row 167 columns 54–54, row 167 columns 55–55), each a sum of
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

theorem rows22240R_4662 : rowsJ2 167 168 0 39 ≤ 15831172030245 := by decide +kernel

theorem rows22240R_4663 : rowsJ2 167 168 39 41 ≤ 13912650791464 := by decide +kernel

theorem rows22240R_4664 : rowsJ2 167 168 41 43 ≤ 18776853755723 := by decide +kernel

theorem rows22240R_4665 : rowsJ2 167 168 43 44 ≤ 11386410886199 := by decide +kernel

theorem rows22240R_4666 : rowsJ2 167 168 44 45 ≤ 12805371256737 := by decide +kernel

theorem rows22240R_4667 : rowsJ2 167 168 45 46 ≤ 14286445047435 := by decide +kernel

theorem rows22240R_4668 : rowsJ2 167 168 46 47 ≤ 15827456420252 := by decide +kernel

theorem rows22240R_4669 : rowsJ2 167 168 47 48 ≤ 17426512808462 := by decide +kernel

theorem rows22240R_4670 : rowsJ2 167 168 48 49 ≤ 19082011652406 := by decide +kernel

theorem rows22240R_4671 : rowsJ2 167 168 49 50 ≤ 20792532301234 := by decide +kernel

theorem rows22240R_4672 : rowsJ2 167 168 50 51 ≤ 20577453699874 := by decide +kernel

theorem rows22240R_4673 : rowsJ2 167 168 51 52 ≤ 18495858266924 := by decide +kernel

theorem rows22240R_4674 : rowsJ2 167 168 52 53 ≤ 16543289025263 := by decide +kernel

theorem rows22240R_4675 : rowsJ2 167 168 53 54 ≤ 14715571121494 := by decide +kernel

theorem rows22240R_4676 : rowsJ2 167 168 54 55 ≤ 13008835633695 := by decide +kernel

theorem rows22240R_4677 : rowsJ2 167 168 55 56 ≤ 11419495187092 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4662
#print axioms SieveCert.rows22240R_4677
