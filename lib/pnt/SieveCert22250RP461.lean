/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5725–5740 of 5796

File 461 of 465: the parts `rows22250R_5725` … `rows22250R_5740` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97077 tests: row 205 columns 34–93, row 205 columns 94–359, row 206 columns
0–30, row 206 columns 31–33, row 206 columns 34–359, row 207 columns 0–29, row 207 columns 30–32, row 207 columns
33–359, row 208 columns 0–29, row 208 columns 30–92, row 208 columns 93–359, row 209 columns 0–29, row 209 columns
30–359, row 210 columns 0–29, row 210 columns 30–359, row 211 columns 0–28), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5725 : rowsJ2 205 206 34 94 ≤ 929701539879166 := by decide +kernel

theorem rows22250R_5726 : rowsJ2 205 206 94 360 ≤ 3750273026559678 := by decide +kernel

theorem rows22250R_5727 : rowsJ2 206 207 0 31 ≤ 22085642846657 := by decide +kernel

theorem rows22250R_5728 : rowsJ2 206 207 31 34 ≤ 38614785545755 := by decide +kernel

theorem rows22250R_5729 : rowsJ2 206 207 34 360 ≤ 4769843426473586 := by decide +kernel

theorem rows22250R_5730 : rowsJ2 207 208 0 30 ≤ 16928509724896 := by decide +kernel

theorem rows22250R_5731 : rowsJ2 207 208 30 33 ≤ 33615964637515 := by decide +kernel

theorem rows22250R_5732 : rowsJ2 207 208 33 360 ≤ 4876879193479871 := by decide +kernel

theorem rows22250R_5733 : rowsJ2 208 209 0 30 ≤ 19842925242301 := by decide +kernel

theorem rows22250R_5734 : rowsJ2 208 209 30 93 ≤ 1109679400817713 := by decide +kernel

theorem rows22250R_5735 : rowsJ2 208 209 93 360 ≤ 3895397768478710 := by decide +kernel

theorem rows22250R_5736 : rowsJ2 209 210 0 30 ≤ 23056444150508 := by decide +kernel

theorem rows22250R_5737 : rowsJ2 209 210 30 360 ≤ 5099897234650805 := by decide +kernel

theorem rows22250R_5738 : rowsJ2 210 211 0 30 ≤ 26660000362028 := by decide +kernel

theorem rows22250R_5739 : rowsJ2 210 211 30 360 ≤ 5194857161433598 := by decide +kernel

theorem rows22250R_5740 : rowsJ2 211 212 0 29 ≤ 20727309296835 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5725
#print axioms SieveCert.rows22250R_5740
