/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 117–132 of 4715

File 8 of 351: the parts `rows22250R_117` … `rows22250R_132` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98465 tests: row 30 columns 21–22, row 30 columns 23–23, row 30 columns
24–24, row 30 columns 25–25, row 30 columns 26–26, row 30 columns 27–27, row 30 columns 28–28, row 30 columns 29–29,
row 30 columns 30–339, row 31 columns 0–13, row 31 columns 14–16, row 31 columns 17–18, row 31 columns 19–20, row 31
columns 21–22, row 31 columns 23–24, row 31 columns 25–25), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_117 : rowsJ2 30 31 21 23 ≤ 2953421875383 := by decide +kernel

theorem rows22250R_118 : rowsJ2 30 31 23 24 ≤ 1486256231565 := by decide +kernel

theorem rows22250R_119 : rowsJ2 30 31 24 25 ≤ 1439838080142 := by decide +kernel

theorem rows22250R_120 : rowsJ2 30 31 25 26 ≤ 1378630864482 := by decide +kernel

theorem rows22250R_121 : rowsJ2 30 31 26 27 ≤ 1303134364539 := by decide +kernel

theorem rows22250R_122 : rowsJ2 30 31 27 28 ≤ 1220683602440 := by decide +kernel

theorem rows22250R_123 : rowsJ2 30 31 28 29 ≤ 1128986656227 := by decide +kernel

theorem rows22250R_124 : rowsJ2 30 31 29 30 ≤ 1051317475699 := by decide +kernel

theorem rows22250R_125 : rowsJ2 30 31 30 340 ≤ 984082706140 := by decide +kernel

theorem rows22250R_126 : rowsJ2 31 32 0 14 ≤ 703028634083 := by decide +kernel

theorem rows22250R_127 : rowsJ2 31 32 14 17 ≤ 1890803153449 := by decide +kernel

theorem rows22250R_128 : rowsJ2 31 32 17 19 ≤ 2229188819558 := by decide +kernel

theorem rows22250R_129 : rowsJ2 31 32 19 21 ≤ 2683537691254 := by decide +kernel

theorem rows22250R_130 : rowsJ2 31 32 21 23 ≤ 2851257588430 := by decide +kernel

theorem rows22250R_131 : rowsJ2 31 32 23 25 ≤ 2766287633702 := by decide +kernel

theorem rows22250R_132 : rowsJ2 31 32 25 26 ≤ 1288639405961 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_117
#print axioms SieveCert.rows22250R_132
