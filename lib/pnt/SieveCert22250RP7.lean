/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 97–113 of 5796

File 7 of 465: the parts `rows22250R_97` … `rows22250R_113` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 95615 tests: row 28 columns 25–25, row 28 columns 26–26, row 28 columns
27–27, row 28 columns 28–359, row 29 columns 0–13, row 29 columns 14–16, row 29 columns 17–18, row 29 columns 19–19,
row 29 columns 20–20, row 29 columns 21–21, row 29 columns 22–22, row 29 columns 23–23, row 29 columns 24–24, row 29
columns 25–25, row 29 columns 26–26, row 29 columns 27–27, row 29 columns 28–28), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_97 : rowsJ2 28 29 25 26 ≤ 1404036174664 := by decide +kernel

theorem rows22250R_98 : rowsJ2 28 29 26 27 ≤ 1397103733235 := by decide +kernel

theorem rows22250R_99 : rowsJ2 28 29 27 28 ≤ 1360242209716 := by decide +kernel

theorem rows22250R_100 : rowsJ2 28 29 28 360 ≤ 1308467577445 := by decide +kernel

theorem rows22250R_101 : rowsJ2 29 30 0 14 ≤ 694337769528 := by decide +kernel

theorem rows22250R_102 : rowsJ2 29 30 14 17 ≤ 790922027734 := by decide +kernel

theorem rows22250R_103 : rowsJ2 29 30 17 19 ≤ 1377983359992 := by decide +kernel

theorem rows22250R_104 : rowsJ2 29 30 19 20 ≤ 952649348297 := by decide +kernel

theorem rows22250R_105 : rowsJ2 29 30 20 21 ≤ 1096319349994 := by decide +kernel

theorem rows22250R_106 : rowsJ2 29 30 21 22 ≤ 1216737624987 := by decide +kernel

theorem rows22250R_107 : rowsJ2 29 30 22 23 ≤ 1293712561913 := by decide +kernel

theorem rows22250R_108 : rowsJ2 29 30 23 24 ≤ 1332394591992 := by decide +kernel

theorem rows22250R_109 : rowsJ2 29 30 24 25 ≤ 1346184957457 := by decide +kernel

theorem rows22250R_110 : rowsJ2 29 30 25 26 ≤ 1351836692399 := by decide +kernel

theorem rows22250R_111 : rowsJ2 29 30 26 27 ≤ 1330448379969 := by decide +kernel

theorem rows22250R_112 : rowsJ2 29 30 27 28 ≤ 1289082342637 := by decide +kernel

theorem rows22250R_113 : rowsJ2 29 30 28 29 ≤ 1233244596710 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_97
#print axioms SieveCert.rows22250R_113
