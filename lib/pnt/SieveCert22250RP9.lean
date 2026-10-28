/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 133–147 of 4715

File 9 of 351: the parts `rows22250R_133` … `rows22250R_147` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 97116 in units of a depth-4 test: row 31 columns 26–26, row 31 columns
27–27, row 31 columns 28–28, row 31 columns 29–29, row 31 columns 30–30, row 31 columns 31–339, row 32 columns 0–13,
row 32 columns 14–16, row 32 columns 17–18, row 32 columns 19–20, row 32 columns 21–22, row 32 columns 23–24, row 32
columns 25–25, row 32 columns 26–26, row 32 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_133 : rowsJ2 31 32 26 27 ≤ 1213043586609 := by decide +kernel

theorem rows22250R_134 : rowsJ2 31 32 27 28 ≤ 1124745499164 := by decide +kernel

theorem rows22250R_135 : rowsJ2 31 32 28 29 ≤ 1039782895050 := by decide +kernel

theorem rows22250R_136 : rowsJ2 31 32 29 30 ≤ 962203373798 := by decide +kernel

theorem rows22250R_137 : rowsJ2 31 32 30 31 ≤ 912783556278 := by decide +kernel

theorem rows22250R_138 : rowsJ2 31 32 31 340 ≤ 878911622029 := by decide +kernel

theorem rows22250R_139 : rowsJ2 32 33 0 14 ≤ 703619682927 := by decide +kernel

theorem rows22250R_140 : rowsJ2 32 33 14 17 ≤ 1979513455341 := by decide +kernel

theorem rows22250R_141 : rowsJ2 32 33 17 19 ≤ 2237714868087 := by decide +kernel

theorem rows22250R_142 : rowsJ2 32 33 19 21 ≤ 2617176962004 := by decide +kernel

theorem rows22250R_143 : rowsJ2 32 33 21 23 ≤ 2741356300210 := by decide +kernel

theorem rows22250R_144 : rowsJ2 32 33 23 25 ≤ 2601215958535 := by decide +kernel

theorem rows22250R_145 : rowsJ2 32 33 25 26 ≤ 1202612175371 := by decide +kernel

theorem rows22250R_146 : rowsJ2 32 33 26 27 ≤ 1120402433854 := by decide +kernel

theorem rows22250R_147 : rowsJ2 32 33 27 28 ≤ 1033405236823 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_133
#print axioms SieveCert.rows22250R_147
