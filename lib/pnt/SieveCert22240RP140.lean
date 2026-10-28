/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1483–1491 of 5066

File 140 of 387: the parts `rows22240R_1483` … `rows22240R_1491` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 99630 in units of a depth-4 test: row 72 columns 54–54, row 72 columns
55–55, row 72 columns 56–56, row 72 columns 57–57, row 72 columns 58–58, row 72 columns 59–59, row 72 columns 60–60,
row 72 columns 61–61, row 72 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1483 : rowsJ2 72 73 54 55 ≤ 5111604596448 := by decide +kernel

theorem rows22240R_1484 : rowsJ2 72 73 55 56 ≤ 5315026392861 := by decide +kernel

theorem rows22240R_1485 : rowsJ2 72 73 56 57 ≤ 4975915318357 := by decide +kernel

theorem rows22240R_1486 : rowsJ2 72 73 57 58 ≤ 4576971340990 := by decide +kernel

theorem rows22240R_1487 : rowsJ2 72 73 58 59 ≤ 4233791616145 := by decide +kernel

theorem rows22240R_1488 : rowsJ2 72 73 59 60 ≤ 3894199456608 := by decide +kernel

theorem rows22240R_1489 : rowsJ2 72 73 60 61 ≤ 3610328169241 := by decide +kernel

theorem rows22240R_1490 : rowsJ2 72 73 61 62 ≤ 3329339634733 := by decide +kernel

theorem rows22240R_1491 : rowsJ2 72 73 62 63 ≤ 3104160558503 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1483
#print axioms SieveCert.rows22240R_1491
