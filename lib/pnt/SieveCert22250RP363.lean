/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4385–4398 of 5796

File 363 of 465: the parts `rows22250R_4385` … `rows22250R_4398` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93930 tests: row 141 columns 72–72, row 141 columns 73–73, row 141 columns
74–74, row 141 columns 75–75, row 141 columns 76–76, row 141 columns 77–77, row 141 columns 78–78, row 141 columns
79–79, row 141 columns 80–80, row 141 columns 81–82, row 141 columns 83–84, row 141 columns 85–87, row 141 columns
88–91, row 141 columns 92–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4385 : rowsJ2 141 142 72 73 ≤ 7150586077105 := by decide +kernel

theorem rows22250R_4386 : rowsJ2 141 142 73 74 ≤ 6408186672195 := by decide +kernel

theorem rows22250R_4387 : rowsJ2 141 142 74 75 ≤ 5720471630402 := by decide +kernel

theorem rows22250R_4388 : rowsJ2 141 142 75 76 ≤ 5068305507007 := by decide +kernel

theorem rows22250R_4389 : rowsJ2 141 142 76 77 ≤ 4468546801525 := by decide +kernel

theorem rows22250R_4390 : rowsJ2 141 142 77 78 ≤ 3901972509457 := by decide +kernel

theorem rows22250R_4391 : rowsJ2 141 142 78 79 ≤ 3385776004688 := by decide +kernel

theorem rows22250R_4392 : rowsJ2 141 142 79 80 ≤ 2900623614126 := by decide +kernel

theorem rows22250R_4393 : rowsJ2 141 142 80 81 ≤ 2464045240242 := by decide +kernel

theorem rows22250R_4394 : rowsJ2 141 142 81 83 ≤ 3752655750929 := by decide +kernel

theorem rows22250R_4395 : rowsJ2 141 142 83 85 ≤ 2438325932770 := by decide +kernel

theorem rows22250R_4396 : rowsJ2 141 142 85 88 ≤ 2664807191232 := by decide +kernel

theorem rows22250R_4397 : rowsJ2 141 142 88 92 ≤ 14663450792470 := by decide +kernel

theorem rows22250R_4398 : rowsJ2 141 142 92 360 ≤ 477995608045755 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4385
#print axioms SieveCert.rows22250R_4398
