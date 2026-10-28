/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1434–1441 of 5066

File 136 of 387: the parts `rows22240R_1434` … `rows22240R_1441` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 93180 in units of a depth-4 test: row 71 columns 54–54, row 71 columns
55–55, row 71 columns 56–56, row 71 columns 57–57, row 71 columns 58–58, row 71 columns 59–59, row 71 columns 60–60,
row 71 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1434 : rowsJ2 71 72 54 55 ≤ 5526588406219 := by decide +kernel

theorem rows22240R_1435 : rowsJ2 71 72 55 56 ≤ 5844137303679 := by decide +kernel

theorem rows22240R_1436 : rowsJ2 71 72 56 57 ≤ 5816416710387 := by decide +kernel

theorem rows22240R_1437 : rowsJ2 71 72 57 58 ≤ 5414433522395 := by decide +kernel

theorem rows22240R_1438 : rowsJ2 71 72 58 59 ≤ 5016830675687 := by decide +kernel

theorem rows22240R_1439 : rowsJ2 71 72 59 60 ≤ 4674943641307 := by decide +kernel

theorem rows22240R_1440 : rowsJ2 71 72 60 61 ≤ 4336663559687 := by decide +kernel

theorem rows22240R_1441 : rowsJ2 71 72 61 62 ≤ 4054082085655 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1434
#print axioms SieveCert.rows22240R_1441
