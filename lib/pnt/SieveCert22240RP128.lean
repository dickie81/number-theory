/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1337–1344 of 5066

File 128 of 387: the parts `rows22240R_1337` … `rows22240R_1344` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 98612 in units of a depth-4 test: row 69 columns 54–54, row 69 columns
55–55, row 69 columns 56–56, row 69 columns 57–57, row 69 columns 58–58, row 69 columns 59–59, row 69 columns 60–60,
row 69 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22240R_1337 : rowsJ2 69 70 54 55 ≤ 6303732728801 := by decide +kernel

theorem rows22240R_1338 : rowsJ2 69 70 55 56 ≤ 6796597259914 := by decide +kernel

theorem rows22240R_1339 : rowsJ2 69 70 56 57 ≤ 7321987669622 := by decide +kernel

theorem rows22240R_1340 : rowsJ2 69 70 57 58 ≤ 7292609994979 := by decide +kernel

theorem rows22240R_1341 : rowsJ2 69 70 58 59 ≤ 6837761839030 := by decide +kernel

theorem rows22240R_1342 : rowsJ2 69 70 59 60 ≤ 6438689542503 := by decide +kernel

theorem rows22240R_1343 : rowsJ2 69 70 60 61 ≤ 6044034896087 := by decide +kernel

theorem rows22240R_1344 : rowsJ2 69 70 61 62 ≤ 5705059380434 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1337
#print axioms SieveCert.rows22240R_1344
