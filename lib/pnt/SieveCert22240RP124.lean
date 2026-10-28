/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1290–1296 of 5066

File 124 of 387: the parts `rows22240R_1290` … `rows22240R_1296` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 89024 in units of a depth-4 test: row 68 columns 55–55, row 68 columns
56–56, row 68 columns 57–57, row 68 columns 58–58, row 68 columns 59–59, row 68 columns 60–60, row 68 columns
61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1290 : rowsJ2 68 69 55 56 ≤ 7221442256760 := by decide +kernel

theorem rows22240R_1291 : rowsJ2 68 69 56 57 ≤ 7861929053685 := by decide +kernel

theorem rows22240R_1292 : rowsJ2 68 69 57 58 ≤ 8268576367037 := by decide +kernel

theorem rows22240R_1293 : rowsJ2 68 69 58 59 ≤ 7810083122133 := by decide +kernel

theorem rows22240R_1294 : rowsJ2 68 69 59 60 ≤ 7356837710388 := by decide +kernel

theorem rows22240R_1295 : rowsJ2 68 69 60 61 ≤ 6959340529432 := by decide +kernel

theorem rows22240R_1296 : rowsJ2 68 69 61 62 ≤ 6566284822940 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1290
#print axioms SieveCert.rows22240R_1296
