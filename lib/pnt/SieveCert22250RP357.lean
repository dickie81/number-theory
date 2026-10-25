/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4310–4319 of 5796

File 357 of 465: the parts `rows22250R_4310` … `rows22250R_4319` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 92569 tests: row 139 columns 63–63, row 139 columns 64–64, row 139 columns
65–65, row 139 columns 66–66, row 139 columns 67–67, row 139 columns 68–68, row 139 columns 69–69, row 139 columns
70–70, row 139 columns 71–71, row 139 columns 72–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4310 : rowsJ2 139 140 63 64 ≤ 5003964455713 := by decide +kernel

theorem rows22250R_4311 : rowsJ2 139 140 64 65 ≤ 5608995658687 := by decide +kernel

theorem rows22250R_4312 : rowsJ2 139 140 65 66 ≤ 6159122096036 := by decide +kernel

theorem rows22250R_4313 : rowsJ2 139 140 66 67 ≤ 6671401958183 := by decide +kernel

theorem rows22250R_4314 : rowsJ2 139 140 67 68 ≤ 7128158867349 := by decide +kernel

theorem rows22250R_4315 : rowsJ2 139 140 68 69 ≤ 7546439936471 := by decide +kernel

theorem rows22250R_4316 : rowsJ2 139 140 69 70 ≤ 7908220234278 := by decide +kernel

theorem rows22250R_4317 : rowsJ2 139 140 70 71 ≤ 8230530955642 := by decide +kernel

theorem rows22250R_4318 : rowsJ2 139 140 71 72 ≤ 7956785107815 := by decide +kernel

theorem rows22250R_4319 : rowsJ2 139 140 72 73 ≤ 7177533209532 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4310
#print axioms SieveCert.rows22250R_4319
