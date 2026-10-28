/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 114–129 of 5066

File 8 of 387: the parts `rows22240R_114` … `rows22240R_129` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93797 in units of a depth-4 test: row 29 columns 29–339, row 30 columns
0–13, row 30 columns 14–16, row 30 columns 17–18, row 30 columns 19–19, row 30 columns 20–20, row 30 columns 21–21,
row 30 columns 22–22, row 30 columns 23–23, row 30 columns 24–24, row 30 columns 25–25, row 30 columns 26–26, row 30
columns 27–27, row 30 columns 28–28, row 30 columns 29–29, row 30 columns 30–339), each a sum of refined costs
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

theorem rows22240R_114 : rowsJ2 29 30 29 340 ≤ 1473824850472 := by decide +kernel

theorem rows22240R_115 : rowsJ2 30 31 0 14 ≤ 1234382219789 := by decide +kernel

theorem rows22240R_116 : rowsJ2 30 31 14 17 ≤ 1100376158417 := by decide +kernel

theorem rows22240R_117 : rowsJ2 30 31 17 19 ≤ 1792503891004 := by decide +kernel

theorem rows22240R_118 : rowsJ2 30 31 19 20 ≤ 1200310766476 := by decide +kernel

theorem rows22240R_119 : rowsJ2 30 31 20 21 ≤ 1371112420118 := by decide +kernel

theorem rows22240R_120 : rowsJ2 30 31 21 22 ≤ 1497794035823 := by decide +kernel

theorem rows22240R_121 : rowsJ2 30 31 22 23 ≤ 1575676134586 := by decide +kernel

theorem rows22240R_122 : rowsJ2 30 31 23 24 ≤ 1605818469315 := by decide +kernel

theorem rows22240R_123 : rowsJ2 30 31 24 25 ≤ 1625339187039 := by decide +kernel

theorem rows22240R_124 : rowsJ2 30 31 25 26 ≤ 1618827328219 := by decide +kernel

theorem rows22240R_125 : rowsJ2 30 31 26 27 ≤ 1586738144368 := by decide +kernel

theorem rows22240R_126 : rowsJ2 30 31 27 28 ≤ 1523696622254 := by decide +kernel

theorem rows22240R_127 : rowsJ2 30 31 28 29 ≤ 1455057159462 := by decide +kernel

theorem rows22240R_128 : rowsJ2 30 31 29 30 ≤ 1379778614026 := by decide +kernel

theorem rows22240R_129 : rowsJ2 30 31 30 340 ≤ 1304232487783 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_114
#print axioms SieveCert.rows22240R_129
