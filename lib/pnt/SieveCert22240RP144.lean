/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1535–1544 of 5066

File 144 of 387: the parts `rows22240R_1535` … `rows22240R_1544` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 95880 in units of a depth-4 test: row 73 columns 56–56, row 73 columns
57–57, row 73 columns 58–58, row 73 columns 59–59, row 73 columns 60–60, row 73 columns 61–61, row 73 columns 62–62,
row 73 columns 63–63, row 73 columns 64–64, row 73 columns 65–65), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1535 : rowsJ2 73 74 56 57 ≤ 4205713219506 := by decide +kernel

theorem rows22240R_1536 : rowsJ2 73 74 57 58 ≤ 3861329829987 := by decide +kernel

theorem rows22240R_1537 : rowsJ2 73 74 58 59 ≤ 3520529910669 := by decide +kernel

theorem rows22240R_1538 : rowsJ2 73 74 59 60 ≤ 3235496855667 := by decide +kernel

theorem rows22240R_1539 : rowsJ2 73 74 60 61 ≤ 2953325549343 := by decide +kernel

theorem rows22240R_1540 : rowsJ2 73 74 61 62 ≤ 2726984818637 := by decide +kernel

theorem rows22240R_1541 : rowsJ2 73 74 62 63 ≤ 2502867254252 := by decide +kernel

theorem rows22240R_1542 : rowsJ2 73 74 63 64 ≤ 2272930854655 := by decide +kernel

theorem rows22240R_1543 : rowsJ2 73 74 64 65 ≤ 2045043115775 := by decide +kernel

theorem rows22240R_1544 : rowsJ2 73 74 65 66 ≤ 1810936723742 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1535
#print axioms SieveCert.rows22240R_1544
