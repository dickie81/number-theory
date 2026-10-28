/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 912–921 of 4715

File 85 of 351: the parts `rows22250R_912` … `rows22250R_921` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, work 94711 in units of a depth-4 test: row 60 columns 57–57, row 60 columns
58–58, row 60 columns 59–59, row 60 columns 60–339, row 61 columns 0–17, row 61 columns 18–21, row 61 columns 22–22,
row 61 columns 23–23, row 61 columns 24–24, row 61 columns 25–25), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_912 : rowsJ2 60 61 57 58 ≤ 12908354991919 := by decide +kernel

theorem rows22250R_913 : rowsJ2 60 61 58 59 ≤ 13927230281931 := by decide +kernel

theorem rows22250R_914 : rowsJ2 60 61 59 60 ≤ 14977620831596 := by decide +kernel

theorem rows22250R_915 : rowsJ2 60 61 60 340 ≤ 15054522378259 := by decide +kernel

theorem rows22250R_916 : rowsJ2 61 62 0 18 ≤ 2363864752369 := by decide +kernel

theorem rows22250R_917 : rowsJ2 61 62 18 22 ≤ 198909359936 := by decide +kernel

theorem rows22250R_918 : rowsJ2 61 62 22 23 ≤ 18409406149 := by decide +kernel

theorem rows22250R_919 : rowsJ2 61 62 23 24 ≤ 9215693985 := by decide +kernel

theorem rows22250R_920 : rowsJ2 61 62 24 25 ≤ 4590765580 := by decide +kernel

theorem rows22250R_921 : rowsJ2 61 62 25 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_912
#print axioms SieveCert.rows22250R_921
