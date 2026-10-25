/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 196–209 of 5796

File 13 of 465: the parts `rows22250R_196` … `rows22250R_209` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97639 tests: row 34 columns 33–33, row 34 columns 34–359, row 35 columns
0–13, row 35 columns 14–16, row 35 columns 17–18, row 35 columns 19–20, row 35 columns 21–22, row 35 columns 23–23,
row 35 columns 24–24, row 35 columns 25–25, row 35 columns 26–26, row 35 columns 27–27, row 35 columns 28–28, row 35
columns 29–29), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_196 : rowsJ2 34 35 33 34 ≤ 656459946475 := by decide +kernel

theorem rows22250R_197 : rowsJ2 34 35 34 360 ≤ 676055088998 := by decide +kernel

theorem rows22250R_198 : rowsJ2 35 36 0 14 ≤ 405644781395 := by decide +kernel

theorem rows22250R_199 : rowsJ2 35 36 14 17 ≤ 1289803850130 := by decide +kernel

theorem rows22250R_200 : rowsJ2 35 36 17 19 ≤ 1585473913834 := by decide +kernel

theorem rows22250R_201 : rowsJ2 35 36 19 21 ≤ 1966962067083 := by decide +kernel

theorem rows22250R_202 : rowsJ2 35 36 21 23 ≤ 2114542324294 := by decide +kernel

theorem rows22250R_203 : rowsJ2 35 36 23 24 ≤ 1063216828569 := by decide +kernel

theorem rows22250R_204 : rowsJ2 35 36 24 25 ≤ 1029400370028 := by decide +kernel

theorem rows22250R_205 : rowsJ2 35 36 25 26 ≤ 985149937417 := by decide +kernel

theorem rows22250R_206 : rowsJ2 35 36 26 27 ≤ 930685821626 := by decide +kernel

theorem rows22250R_207 : rowsJ2 35 36 27 28 ≤ 870893863578 := by decide +kernel

theorem rows22250R_208 : rowsJ2 35 36 28 29 ≤ 802022997910 := by decide +kernel

theorem rows22250R_209 : rowsJ2 35 36 29 30 ≤ 739166407702 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_196
#print axioms SieveCert.rows22250R_209
