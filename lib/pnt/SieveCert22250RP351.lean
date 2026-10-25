/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4229–4243 of 5796

File 351 of 465: the parts `rows22250R_4229` … `rows22250R_4243` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98915 tests: row 136 columns 79–79, row 136 columns 80–80, row 136 columns
81–82, row 136 columns 83–84, row 136 columns 85–87, row 136 columns 88–90, row 136 columns 91–93, row 136 columns
94–359, row 137 columns 0–24, row 137 columns 25–28, row 137 columns 29–34, row 137 columns 35–54, row 137 columns
55–58, row 137 columns 59–60, row 137 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4229 : rowsJ2 136 137 79 80 ≤ 2757970746859 := by decide +kernel

theorem rows22250R_4230 : rowsJ2 136 137 80 81 ≤ 2323840751529 := by decide +kernel

theorem rows22250R_4231 : rowsJ2 136 137 81 83 ≤ 3478518550063 := by decide +kernel

theorem rows22250R_4232 : rowsJ2 136 137 83 85 ≤ 2171707356333 := by decide +kernel

theorem rows22250R_4233 : rowsJ2 136 137 85 88 ≤ 2088976205853 := by decide +kernel

theorem rows22250R_4234 : rowsJ2 136 137 88 91 ≤ 6935053297064 := by decide +kernel

theorem rows22250R_4235 : rowsJ2 136 137 91 94 ≤ 16143689783471 := by decide +kernel

theorem rows22250R_4236 : rowsJ2 136 137 94 360 ≤ 723686697734396 := by decide +kernel

theorem rows22250R_4237 : rowsJ2 137 138 0 25 ≤ 2118287174833 := by decide +kernel

theorem rows22250R_4238 : rowsJ2 137 138 25 29 ≤ 11296385446208 := by decide +kernel

theorem rows22250R_4239 : rowsJ2 137 138 29 35 ≤ 7063609735762 := by decide +kernel

theorem rows22250R_4240 : rowsJ2 137 138 35 55 ≤ 1417248595196 := by decide +kernel

theorem rows22250R_4241 : rowsJ2 137 138 55 59 ≤ 5129916945476 := by decide +kernel

theorem rows22250R_4242 : rowsJ2 137 138 59 61 ≤ 4930142461107 := by decide +kernel

theorem rows22250R_4243 : rowsJ2 137 138 61 62 ≤ 3187610057887 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4229
#print axioms SieveCert.rows22250R_4243
