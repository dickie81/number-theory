/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4269–4284 of 4715

File 324 of 351: the parts `rows22250R_4269` … `rows22250R_4284` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94532 tests: row 163 columns 53–53, row 163 columns 54–54, row 163 columns
55–55, row 163 columns 56–56, row 163 columns 57–57, row 163 columns 58–59, row 163 columns 60–62, row 163 columns
63–339, row 164 columns 0–38, row 164 columns 39–41, row 164 columns 42–43, row 164 columns 44–44, row 164 columns
45–45, row 164 columns 46–46, row 164 columns 47–47, row 164 columns 48–48), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4269 : rowsJ2 163 164 53 54 ≤ 14751942282681 := by decide +kernel

theorem rows22250R_4270 : rowsJ2 163 164 54 55 ≤ 13085230011246 := by decide +kernel

theorem rows22250R_4271 : rowsJ2 163 164 55 56 ≤ 11530521036666 := by decide +kernel

theorem rows22250R_4272 : rowsJ2 163 164 56 57 ≤ 10084678074583 := by decide +kernel

theorem rows22250R_4273 : rowsJ2 163 164 57 58 ≤ 8744809957333 := by decide +kernel

theorem rows22250R_4274 : rowsJ2 163 164 58 60 ≤ 13880854763655 := by decide +kernel

theorem rows22250R_4275 : rowsJ2 163 164 60 63 ≤ 13280594416416 := by decide +kernel

theorem rows22250R_4276 : rowsJ2 163 164 63 340 ≤ 2639613584138816 := by decide +kernel

theorem rows22250R_4277 : rowsJ2 164 165 0 39 ≤ 12318810952120 := by decide +kernel

theorem rows22250R_4278 : rowsJ2 164 165 39 42 ≤ 18275823000384 := by decide +kernel

theorem rows22250R_4279 : rowsJ2 164 165 42 44 ≤ 17854156223680 := by decide +kernel

theorem rows22250R_4280 : rowsJ2 164 165 44 45 ≤ 10830221620131 := by decide +kernel

theorem rows22250R_4281 : rowsJ2 164 165 45 46 ≤ 12182230106729 := by decide +kernel

theorem rows22250R_4282 : rowsJ2 164 165 46 47 ≤ 13593692132881 := by decide +kernel

theorem rows22250R_4283 : rowsJ2 164 165 47 48 ≤ 15062515862181 := by decide +kernel

theorem rows22250R_4284 : rowsJ2 164 165 48 49 ≤ 16586839023719 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4269
#print axioms SieveCert.rows22250R_4284
