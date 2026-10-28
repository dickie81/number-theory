/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1150–1156 of 5066

File 112 of 387: the parts `rows22240R_1150` … `rows22240R_1156` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 94904 in units of a depth-4 test: row 65 columns 56–56, row 65 columns
57–57, row 65 columns 58–58, row 65 columns 59–59, row 65 columns 60–60, row 65 columns 61–61, row 65 columns
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

theorem rows22240R_1150 : rowsJ2 65 66 56 57 ≤ 9278980572042 := by decide +kernel

theorem rows22240R_1151 : rowsJ2 65 66 57 58 ≤ 9980335948775 := by decide +kernel

theorem rows22240R_1152 : rowsJ2 65 66 58 59 ≤ 10448420581864 := by decide +kernel

theorem rows22240R_1153 : rowsJ2 65 66 59 60 ≤ 10430177538557 := by decide +kernel

theorem rows22240R_1154 : rowsJ2 65 66 60 61 ≤ 9921043618724 := by decide +kernel

theorem rows22240R_1155 : rowsJ2 65 66 61 62 ≤ 9467780835662 := by decide +kernel

theorem rows22240R_1156 : rowsJ2 65 66 62 63 ≤ 9019816112155 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1150
#print axioms SieveCert.rows22240R_1156
