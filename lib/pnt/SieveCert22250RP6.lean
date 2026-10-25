/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 79–96 of 5796

File 6 of 465: the parts `rows22250R_79` … `rows22250R_96` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 99693 tests: row 27 columns 19–19, row 27 columns 20–20, row 27 columns
21–21, row 27 columns 22–22, row 27 columns 23–23, row 27 columns 24–24, row 27 columns 25–25, row 27 columns 26–26,
row 27 columns 27–359, row 28 columns 0–13, row 28 columns 14–16, row 28 columns 17–18, row 28 columns 19–19, row 28
columns 20–20, row 28 columns 21–21, row 28 columns 22–22, row 28 columns 23–23, row 28 columns 24–24), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_79 : rowsJ2 27 28 19 20 ≤ 919237743019 := by decide +kernel

theorem rows22250R_80 : rowsJ2 27 28 20 21 ≤ 1089774945357 := by decide +kernel

theorem rows22250R_81 : rowsJ2 27 28 21 22 ≤ 1233765231756 := by decide +kernel

theorem rows22250R_82 : rowsJ2 27 28 22 23 ≤ 1345134502641 := by decide +kernel

theorem rows22250R_83 : rowsJ2 27 28 23 24 ≤ 1420342429770 := by decide +kernel

theorem rows22250R_84 : rowsJ2 27 28 24 25 ≤ 1450457904014 := by decide +kernel

theorem rows22250R_85 : rowsJ2 27 28 25 26 ≤ 1462843083800 := by decide +kernel

theorem rows22250R_86 : rowsJ2 27 28 26 27 ≤ 1457464802388 := by decide +kernel

theorem rows22250R_87 : rowsJ2 27 28 27 360 ≤ 1434922615564 := by decide +kernel

theorem rows22250R_88 : rowsJ2 28 29 0 14 ≤ 804054365870 := by decide +kernel

theorem rows22250R_89 : rowsJ2 28 29 14 17 ≤ 704859640339 := by decide +kernel

theorem rows22250R_90 : rowsJ2 28 29 17 19 ≤ 1313777303671 := by decide +kernel

theorem rows22250R_91 : rowsJ2 28 29 19 20 ≤ 939981528649 := by decide +kernel

theorem rows22250R_92 : rowsJ2 28 29 20 21 ≤ 1095409008636 := by decide +kernel

theorem rows22250R_93 : rowsJ2 28 29 21 22 ≤ 1225279203714 := by decide +kernel

theorem rows22250R_94 : rowsJ2 28 29 22 23 ≤ 1324395223153 := by decide +kernel

theorem rows22250R_95 : rowsJ2 28 29 23 24 ≤ 1377743106023 := by decide +kernel

theorem rows22250R_96 : rowsJ2 28 29 24 25 ≤ 1399912105825 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_79
#print axioms SieveCert.rows22250R_96
