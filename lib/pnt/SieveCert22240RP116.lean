/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1196–1202 of 5066

File 116 of 387: the parts `rows22240R_1196` … `rows22240R_1202` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 92708 in units of a depth-4 test: row 66 columns 56–56, row 66 columns
57–57, row 66 columns 58–58, row 66 columns 59–59, row 66 columns 60–60, row 66 columns 61–61, row 66 columns
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

theorem rows22240R_1196 : rowsJ2 66 67 56 57 ≤ 8839715037879 := by decide +kernel

theorem rows22240R_1197 : rowsJ2 66 67 57 58 ≤ 9427025172328 := by decide +kernel

theorem rows22240R_1198 : rowsJ2 66 67 58 59 ≤ 9829495642326 := by decide +kernel

theorem rows22240R_1199 : rowsJ2 66 67 59 60 ≤ 9318524549350 := by decide +kernel

theorem rows22240R_1200 : rowsJ2 66 67 60 61 ≤ 8863430654091 := by decide +kernel

theorem rows22240R_1201 : rowsJ2 66 67 61 62 ≤ 8413605769645 := by decide +kernel

theorem rows22240R_1202 : rowsJ2 66 67 62 63 ≤ 8019510642974 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1196
#print axioms SieveCert.rows22240R_1202
