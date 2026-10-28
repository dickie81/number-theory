/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1780–1791 of 5066

File 162 of 387: the parts `rows22240R_1780` … `rows22240R_1791` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95000 in units of a depth-4 test: row 78 columns 54–54, row 78 columns
55–55, row 78 columns 56–56, row 78 columns 57–57, row 78 columns 58–58, row 78 columns 59–59, row 78 columns 60–60,
row 78 columns 61–61, row 78 columns 62–62, row 78 columns 63–63, row 78 columns 64–64, row 78 columns 65–65), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1780 : rowsJ2 78 79 54 55 ≤ 1843316022563 := by decide +kernel

theorem rows22240R_1781 : rowsJ2 78 79 55 56 ≤ 1617951856010 := by decide +kernel

theorem rows22240R_1782 : rowsJ2 78 79 56 57 ≤ 1448285612089 := by decide +kernel

theorem rows22240R_1783 : rowsJ2 78 79 57 58 ≤ 1219681169533 := by decide +kernel

theorem rows22240R_1784 : rowsJ2 78 79 58 59 ≤ 1047358278441 := by decide +kernel

theorem rows22240R_1785 : rowsJ2 78 79 59 60 ≤ 876584720965 := by decide +kernel

theorem rows22240R_1786 : rowsJ2 78 79 60 61 ≤ 762300974713 := by decide +kernel

theorem rows22240R_1787 : rowsJ2 78 79 61 62 ≤ 649014152234 := by decide +kernel

theorem rows22240R_1788 : rowsJ2 78 79 62 63 ≤ 592557862693 := by decide +kernel

theorem rows22240R_1789 : rowsJ2 78 79 63 64 ≤ 477260940126 := by decide +kernel

theorem rows22240R_1790 : rowsJ2 78 79 64 65 ≤ 419636071449 := by decide +kernel

theorem rows22240R_1791 : rowsJ2 78 79 65 66 ≤ 302077139955 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1780
#print axioms SieveCert.rows22240R_1791
