/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4359–4374 of 5796

File 361 of 465: the parts `rows22250R_4359` … `rows22250R_4374` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96917 tests: row 140 columns 79–79, row 140 columns 80–80, row 140 columns
81–82, row 140 columns 83–84, row 140 columns 85–87, row 140 columns 88–90, row 140 columns 91–359, row 141 columns
0–23, row 141 columns 24–28, row 141 columns 29–50, row 141 columns 51–55, row 141 columns 56–57, row 141 columns
58–58, row 141 columns 59–59, row 141 columns 60–60, row 141 columns 61–61), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4359 : rowsJ2 140 141 79 80 ≤ 2939035593827 := by decide +kernel

theorem rows22250R_4360 : rowsJ2 140 141 80 81 ≤ 2502874085244 := by decide +kernel

theorem rows22250R_4361 : rowsJ2 140 141 81 83 ≤ 3831359558183 := by decide +kernel

theorem rows22250R_4362 : rowsJ2 140 141 83 85 ≤ 2518268454540 := by decide +kernel

theorem rows22250R_4363 : rowsJ2 140 141 85 88 ≤ 2765677430067 := by decide +kernel

theorem rows22250R_4364 : rowsJ2 140 141 88 91 ≤ 8963606125437 := by decide +kernel

theorem rows22250R_4365 : rowsJ2 140 141 91 360 ≤ 561768482412027 := by decide +kernel

theorem rows22250R_4366 : rowsJ2 141 142 0 24 ≤ 1967034626667 := by decide +kernel

theorem rows22250R_4367 : rowsJ2 141 142 24 29 ≤ 8061878391772 := by decide +kernel

theorem rows22250R_4368 : rowsJ2 141 142 29 51 ≤ 1686255557265 := by decide +kernel

theorem rows22250R_4369 : rowsJ2 141 142 51 56 ≤ 4425442620821 := by decide +kernel

theorem rows22250R_4370 : rowsJ2 141 142 56 58 ≤ 4288730309701 := by decide +kernel

theorem rows22250R_4371 : rowsJ2 141 142 58 59 ≤ 2851033155288 := by decide +kernel

theorem rows22250R_4372 : rowsJ2 141 142 59 60 ≤ 3372519169773 := by decide +kernel

theorem rows22250R_4373 : rowsJ2 141 142 60 61 ≤ 3929868229273 := by decide +kernel

theorem rows22250R_4374 : rowsJ2 141 142 61 62 ≤ 4521669281363 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4359
#print axioms SieveCert.rows22250R_4374
