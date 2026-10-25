/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1787–1797 of 5796

File 176 of 465: the parts `rows22250R_1787` … `rows22250R_1797` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95531 tests: row 78 columns 61–61, row 78 columns 62–62, row 78 columns
63–63, row 78 columns 64–64, row 78 columns 65–65, row 78 columns 66–66, row 78 columns 67–67, row 78 columns 68–68,
row 78 columns 69–69, row 78 columns 70–70, row 78 columns 71–71), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1787 : rowsJ2 78 79 61 62 ≤ 2285929018669 := by decide +kernel

theorem rows22250R_1788 : rowsJ2 78 79 62 63 ≤ 2102085915739 := by decide +kernel

theorem rows22250R_1789 : rowsJ2 78 79 63 64 ≤ 1869697544942 := by decide +kernel

theorem rows22250R_1790 : rowsJ2 78 79 64 65 ≤ 1683044828191 := by decide +kernel

theorem rows22250R_1791 : rowsJ2 78 79 65 66 ≤ 1446907229757 := by decide +kernel

theorem rows22250R_1792 : rowsJ2 78 79 66 67 ≤ 1256987681771 := by decide +kernel

theorem rows22250R_1793 : rowsJ2 78 79 67 68 ≤ 1068509906218 := by decide +kernel

theorem rows22250R_1794 : rowsJ2 78 79 68 69 ≤ 926479739749 := by decide +kernel

theorem rows22250R_1795 : rowsJ2 78 79 69 70 ≤ 785478014996 := by decide +kernel

theorem rows22250R_1796 : rowsJ2 78 79 70 71 ≤ 691247973087 := by decide +kernel

theorem rows22250R_1797 : rowsJ2 78 79 71 72 ≤ 547489760599 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1787
#print axioms SieveCert.rows22250R_1797
