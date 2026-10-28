/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1111–1122 of 5066

File 109 of 387: the parts `rows22240R_1111` … `rows22240R_1122` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 98784 in units of a depth-4 test: row 64 columns 62–62, row 64 columns
63–63, row 64 columns 64–339, row 65 columns 0–17, row 65 columns 18–20, row 65 columns 21–22, row 65 columns 23–23,
row 65 columns 24–24, row 65 columns 25–25, row 65 columns 26–26, row 65 columns 27–27, row 65 columns 28–28), each
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

theorem rows22240R_1111 : rowsJ2 64 65 62 63 ≤ 10149399345545 := by decide +kernel

theorem rows22240R_1112 : rowsJ2 64 65 63 64 ≤ 9636562489217 := by decide +kernel

theorem rows22240R_1113 : rowsJ2 64 65 64 340 ≤ 9179940715330 := by decide +kernel

theorem rows22240R_1114 : rowsJ2 65 66 0 18 ≤ 2336655174683 := by decide +kernel

theorem rows22240R_1115 : rowsJ2 65 66 18 21 ≤ 201724520979 := by decide +kernel

theorem rows22240R_1116 : rowsJ2 65 66 21 23 ≤ 62753745225 := by decide +kernel

theorem rows22240R_1117 : rowsJ2 65 66 23 24 ≤ 16694565871 := by decide +kernel

theorem rows22240R_1118 : rowsJ2 65 66 24 25 ≤ 8359373245 := by decide +kernel

theorem rows22240R_1119 : rowsJ2 65 66 25 26 ≤ 4165061186 := by decide +kernel

theorem rows22240R_1120 : rowsJ2 65 66 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1121 : rowsJ2 65 66 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1122 : rowsJ2 65 66 28 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1111
#print axioms SieveCert.rows22240R_1122
