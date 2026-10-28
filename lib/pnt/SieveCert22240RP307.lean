/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3877–3891 of 5066

File 307 of 387: the parts `rows22240R_3877` … `rows22240R_3891` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99141 in units of a depth-4 test: row 134 columns 83–85, row 134
columns 86–339, row 135 columns 0–23, row 135 columns 24–30, row 135 columns 31–50, row 135 columns 51–53, row 135
columns 54–55, row 135 columns 56–56, row 135 columns 57–57, row 135 columns 58–58, row 135 columns 59–59, row 135
columns 60–60, row 135 columns 61–61, row 135 columns 62–62, row 135 columns 63–63), each a sum of refined costs
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

theorem rows22240R_3877 : rowsJ2 134 135 83 86 ≤ 14757884293547 := by decide +kernel

theorem rows22240R_3878 : rowsJ2 134 135 86 340 ≤ 618221220690063 := by decide +kernel

theorem rows22240R_3879 : rowsJ2 135 136 0 24 ≤ 4409634362085 := by decide +kernel

theorem rows22240R_3880 : rowsJ2 135 136 24 31 ≤ 11569896352697 := by decide +kernel

theorem rows22240R_3881 : rowsJ2 135 136 31 51 ≤ 2674824157046 := by decide +kernel

theorem rows22240R_3882 : rowsJ2 135 136 51 54 ≤ 5829123885530 := by decide +kernel

theorem rows22240R_3883 : rowsJ2 135 136 54 56 ≤ 6607162767538 := by decide +kernel

theorem rows22240R_3884 : rowsJ2 135 136 56 57 ≤ 4266103958134 := by decide +kernel

theorem rows22240R_3885 : rowsJ2 135 136 57 58 ≤ 4967900265232 := by decide +kernel

theorem rows22240R_3886 : rowsJ2 135 136 58 59 ≤ 5712433999053 := by decide +kernel

theorem rows22240R_3887 : rowsJ2 135 136 59 60 ≤ 6497962587285 := by decide +kernel

theorem rows22240R_3888 : rowsJ2 135 136 60 61 ≤ 7322843018469 := by decide +kernel

theorem rows22240R_3889 : rowsJ2 135 136 61 62 ≤ 8164955107172 := by decide +kernel

theorem rows22240R_3890 : rowsJ2 135 136 62 63 ≤ 8961848301032 := by decide +kernel

theorem rows22240R_3891 : rowsJ2 135 136 63 64 ≤ 9692498281864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3877
#print axioms SieveCert.rows22240R_3891
