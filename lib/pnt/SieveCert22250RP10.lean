/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 148–161 of 4715

File 10 of 351: the parts `rows22250R_148` … `rows22250R_161` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 99831 in units of a depth-4 test: row 32 columns 28–28, row 32 columns
29–29, row 32 columns 30–30, row 32 columns 31–31, row 32 columns 32–339, row 33 columns 0–13, row 33 columns 14–16,
row 33 columns 17–18, row 33 columns 19–20, row 33 columns 21–22, row 33 columns 23–24, row 33 columns 25–25, row 33
columns 26–26, row 33 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_148 : rowsJ2 32 33 28 29 ≤ 950175540439 := by decide +kernel

theorem rows22250R_149 : rowsJ2 32 33 29 30 ≤ 888053723722 := by decide +kernel

theorem rows22250R_150 : rowsJ2 32 33 30 31 ≤ 839998635057 := by decide +kernel

theorem rows22250R_151 : rowsJ2 32 33 31 32 ≤ 825660137946 := by decide +kernel

theorem rows22250R_152 : rowsJ2 32 33 32 340 ≤ 841461388419 := by decide +kernel

theorem rows22250R_153 : rowsJ2 33 34 0 14 ≤ 721382476683 := by decide +kernel

theorem rows22250R_154 : rowsJ2 33 34 14 17 ≤ 2062513903834 := by decide +kernel

theorem rows22250R_155 : rowsJ2 33 34 17 19 ≤ 2234207927330 := by decide +kernel

theorem rows22250R_156 : rowsJ2 33 34 19 21 ≤ 2547220479070 := by decide +kernel

theorem rows22250R_157 : rowsJ2 33 34 21 23 ≤ 2619074432897 := by decide +kernel

theorem rows22250R_158 : rowsJ2 33 34 23 25 ≤ 2437492701585 := by decide +kernel

theorem rows22250R_159 : rowsJ2 33 34 25 26 ≤ 1113974118295 := by decide +kernel

theorem rows22250R_160 : rowsJ2 33 34 26 27 ≤ 1032318404270 := by decide +kernel

theorem rows22250R_161 : rowsJ2 33 34 27 28 ≤ 943205664803 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_148
#print axioms SieveCert.rows22250R_161
