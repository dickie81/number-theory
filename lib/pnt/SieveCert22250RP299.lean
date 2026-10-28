/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3902–3915 of 4715

File 299 of 351: the parts `rows22250R_3902` … `rows22250R_3915` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 94430 in units of a depth-4 test: row 146 columns 78–339, row 147
columns 0–43, row 147 columns 44–47, row 147 columns 48–49, row 147 columns 50–50, row 147 columns 51–51, row 147
columns 52–52, row 147 columns 53–53, row 147 columns 54–54, row 147 columns 55–55, row 147 columns 56–56, row 147
columns 57–57, row 147 columns 58–58, row 147 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3902 : rowsJ2 146 147 78 340 ≤ 1505993361459718 := by decide +kernel

theorem rows22250R_3903 : rowsJ2 147 148 0 44 ≤ 2637466742654 := by decide +kernel

theorem rows22250R_3904 : rowsJ2 147 148 44 48 ≤ 9678442258565 := by decide +kernel

theorem rows22250R_3905 : rowsJ2 147 148 48 50 ≤ 8887186122619 := by decide +kernel

theorem rows22250R_3906 : rowsJ2 147 148 50 51 ≤ 5657988450362 := by decide +kernel

theorem rows22250R_3907 : rowsJ2 147 148 51 52 ≤ 6537847267192 := by decide +kernel

theorem rows22250R_3908 : rowsJ2 147 148 52 53 ≤ 7467637179273 := by decide +kernel

theorem rows22250R_3909 : rowsJ2 147 148 53 54 ≤ 8445359292188 := by decide +kernel

theorem rows22250R_3910 : rowsJ2 147 148 54 55 ≤ 9469180960158 := by decide +kernel

theorem rows22250R_3911 : rowsJ2 147 148 55 56 ≤ 10537426887997 := by decide +kernel

theorem rows22250R_3912 : rowsJ2 147 148 56 57 ≤ 11648571045205 := by decide +kernel

theorem rows22250R_3913 : rowsJ2 147 148 57 58 ≤ 12801229339280 := by decide +kernel

theorem rows22250R_3914 : rowsJ2 147 148 58 59 ≤ 13994153001454 := by decide +kernel

theorem rows22250R_3915 : rowsJ2 147 148 59 60 ≤ 13862172715542 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3902
#print axioms SieveCert.rows22250R_3915
