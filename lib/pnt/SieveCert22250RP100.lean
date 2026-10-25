/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1090–1105 of 4715

File 100 of 351: the parts `rows22250R_1090` … `rows22250R_1105` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98034 tests: row 65 columns 0–17, row 65 columns 18–20, row 65 columns
21–22, row 65 columns 23–23, row 65 columns 24–24, row 65 columns 25–25, row 65 columns 26–26, row 65 columns 27–27,
row 65 columns 28–28, row 65 columns 29–29, row 65 columns 30–30, row 65 columns 31–31, row 65 columns 32–32, row 65
columns 33–33, row 65 columns 34–34, row 65 columns 35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1090 : rowsJ2 65 66 0 18 ≤ 1618967317770 := by decide +kernel

theorem rows22250R_1091 : rowsJ2 65 66 18 21 ≤ 32960013372 := by decide +kernel

theorem rows22250R_1092 : rowsJ2 65 66 21 23 ≤ 0 := by decide +kernel

theorem rows22250R_1093 : rowsJ2 65 66 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1094 : rowsJ2 65 66 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1095 : rowsJ2 65 66 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1096 : rowsJ2 65 66 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1097 : rowsJ2 65 66 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1098 : rowsJ2 65 66 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1099 : rowsJ2 65 66 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1100 : rowsJ2 65 66 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1101 : rowsJ2 65 66 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1102 : rowsJ2 65 66 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1103 : rowsJ2 65 66 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1104 : rowsJ2 65 66 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1105 : rowsJ2 65 66 35 36 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1090
#print axioms SieveCert.rows22250R_1105
