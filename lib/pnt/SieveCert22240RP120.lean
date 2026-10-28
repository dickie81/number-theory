/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1243–1249 of 5066

File 120 of 387: the parts `rows22240R_1243` … `rows22240R_1249` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 90063 in units of a depth-4 test: row 67 columns 56–56, row 67 columns
57–57, row 67 columns 58–58, row 67 columns 59–59, row 67 columns 60–60, row 67 columns 61–61, row 67 columns
62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22240R_1243 : rowsJ2 67 68 56 57 ≤ 8351058633161 := by decide +kernel

theorem rows22240R_1244 : rowsJ2 67 68 57 58 ≤ 8873215494813 := by decide +kernel

theorem rows22240R_1245 : rowsJ2 67 68 58 59 ≤ 8790395635667 := by decide +kernel

theorem rows22240R_1246 : rowsJ2 67 68 59 60 ≤ 8333567347197 := by decide +kernel

theorem rows22240R_1247 : rowsJ2 67 68 60 61 ≤ 7881995476162 := by decide +kernel

theorem rows22240R_1248 : rowsJ2 67 68 61 62 ≤ 7486156426033 := by decide +kernel

theorem rows22240R_1249 : rowsJ2 67 68 62 63 ≤ 7094786341431 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1243
#print axioms SieveCert.rows22240R_1249
