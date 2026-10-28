/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1157–1168 of 5066

File 113 of 387: the parts `rows22240R_1157` … `rows22240R_1168` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95551 in units of a depth-4 test: row 65 columns 63–63, row 65 columns
64–64, row 65 columns 65–339, row 66 columns 0–17, row 66 columns 18–20, row 66 columns 21–22, row 66 columns 23–23,
row 66 columns 24–24, row 66 columns 25–25, row 66 columns 26–26, row 66 columns 27–27, row 66 columns 28–28), each
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

theorem rows22240R_1157 : rowsJ2 65 66 63 64 ≤ 8561327890918 := by decide +kernel

theorem rows22240R_1158 : rowsJ2 65 66 64 65 ≤ 8107800511125 := by decide +kernel

theorem rows22240R_1159 : rowsJ2 65 66 65 340 ≤ 7642986318495 := by decide +kernel

theorem rows22240R_1160 : rowsJ2 66 67 0 18 ≤ 2156672987175 := by decide +kernel

theorem rows22240R_1161 : rowsJ2 66 67 18 21 ≤ 156126536967 := by decide +kernel

theorem rows22240R_1162 : rowsJ2 66 67 21 23 ≤ 42035395925 := by decide +kernel

theorem rows22240R_1163 : rowsJ2 66 67 23 24 ≤ 8404136134 := by decide +kernel

theorem rows22240R_1164 : rowsJ2 66 67 24 25 ≤ 4186525012 := by decide +kernel

theorem rows22240R_1165 : rowsJ2 66 67 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1166 : rowsJ2 66 67 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1167 : rowsJ2 66 67 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1168 : rowsJ2 66 67 28 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1157
#print axioms SieveCert.rows22240R_1168
