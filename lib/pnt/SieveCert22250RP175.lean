/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1779–1786 of 5796

File 175 of 465: the parts `rows22250R_1779` … `rows22250R_1786` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 98590 tests: row 78 columns 53–53, row 78 columns 54–54, row 78 columns
55–55, row 78 columns 56–56, row 78 columns 57–57, row 78 columns 58–58, row 78 columns 59–59, row 78 columns
60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1779 : rowsJ2 78 79 53 54 ≤ 2634263573103 := by decide +kernel

theorem rows22250R_1780 : rowsJ2 78 79 54 55 ≤ 2868995854013 := by decide +kernel

theorem rows22250R_1781 : rowsJ2 78 79 55 56 ≤ 3069353892914 := by decide +kernel

theorem rows22250R_1782 : rowsJ2 78 79 56 57 ≤ 3326501613411 := by decide +kernel

theorem rows22250R_1783 : rowsJ2 78 79 57 58 ≤ 3102448011330 := by decide +kernel

theorem rows22250R_1784 : rowsJ2 78 79 58 59 ≤ 2922896519140 := by decide +kernel

theorem rows22250R_1785 : rowsJ2 78 79 59 60 ≤ 2696539939541 := by decide +kernel

theorem rows22250R_1786 : rowsJ2 78 79 60 61 ≤ 2515060922276 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1779
#print axioms SieveCert.rows22250R_1786
