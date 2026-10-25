/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 243–251 of 4715

File 19 of 351: the parts `rows22250R_243` … `rows22250R_251` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 97008 tests: row 38 columns 26–26, row 38 columns 27–27, row 38 columns
28–28, row 38 columns 29–29, row 38 columns 30–30, row 38 columns 31–31, row 38 columns 32–32, row 38 columns 33–33,
row 38 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_243 : rowsJ2 38 39 26 27 ≤ 651873478799 := by decide +kernel

theorem rows22250R_244 : rowsJ2 38 39 27 28 ≤ 596948308700 := by decide +kernel

theorem rows22250R_245 : rowsJ2 38 39 28 29 ≤ 554427303084 := by decide +kernel

theorem rows22250R_246 : rowsJ2 38 39 29 30 ≤ 533371710023 := by decide +kernel

theorem rows22250R_247 : rowsJ2 38 39 30 31 ≤ 535626206829 := by decide +kernel

theorem rows22250R_248 : rowsJ2 38 39 31 32 ≤ 570433004117 := by decide +kernel

theorem rows22250R_249 : rowsJ2 38 39 32 33 ≤ 616722437535 := by decide +kernel

theorem rows22250R_250 : rowsJ2 38 39 33 34 ≤ 624469098504 := by decide +kernel

theorem rows22250R_251 : rowsJ2 38 39 34 35 ≤ 612273325619 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_243
#print axioms SieveCert.rows22250R_251
