/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 146–161 of 5066

File 10 of 387: the parts `rows22240R_146` … `rows22240R_161` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93716 in units of a depth-4 test: row 32 columns 0–13, row 32 columns
14–16, row 32 columns 17–18, row 32 columns 19–19, row 32 columns 20–20, row 32 columns 21–21, row 32 columns 22–22,
row 32 columns 23–23, row 32 columns 24–24, row 32 columns 25–25, row 32 columns 26–26, row 32 columns 27–27, row 32
columns 28–28, row 32 columns 29–29, row 32 columns 30–30, row 32 columns 31–31), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_146 : rowsJ2 32 33 0 14 ≤ 969737264909 := by decide +kernel

theorem rows22240R_147 : rowsJ2 32 33 14 17 ≤ 1311767188314 := by decide +kernel

theorem rows22240R_148 : rowsJ2 32 33 17 19 ≤ 1893040410074 := by decide +kernel

theorem rows22240R_149 : rowsJ2 32 33 19 20 ≤ 1213991766674 := by decide +kernel

theorem rows22240R_150 : rowsJ2 32 33 20 21 ≤ 1351861310474 := by decide +kernel

theorem rows22240R_151 : rowsJ2 32 33 21 22 ≤ 1431999981383 := by decide +kernel

theorem rows22240R_152 : rowsJ2 32 33 22 23 ≤ 1476030667920 := by decide +kernel

theorem rows22240R_153 : rowsJ2 32 33 23 24 ≤ 1497251389821 := by decide +kernel

theorem rows22240R_154 : rowsJ2 32 33 24 25 ≤ 1504215475184 := by decide +kernel

theorem rows22240R_155 : rowsJ2 32 33 25 26 ≤ 1473422494393 := by decide +kernel

theorem rows22240R_156 : rowsJ2 32 33 26 27 ≤ 1417339260861 := by decide +kernel

theorem rows22240R_157 : rowsJ2 32 33 27 28 ≤ 1348573352327 := by decide +kernel

theorem rows22240R_158 : rowsJ2 32 33 28 29 ≤ 1276246524880 := by decide +kernel

theorem rows22240R_159 : rowsJ2 32 33 29 30 ≤ 1197878232691 := by decide +kernel

theorem rows22240R_160 : rowsJ2 32 33 30 31 ≤ 1124663500915 := by decide +kernel

theorem rows22240R_161 : rowsJ2 32 33 31 32 ≤ 1067599335004 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_146
#print axioms SieveCert.rows22240R_161
