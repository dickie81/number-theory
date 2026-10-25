/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4363–4378 of 4715

File 330 of 351: the parts `rows22250R_4363` … `rows22250R_4378` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96917 tests: row 168 columns 51–51, row 168 columns 52–52, row 168 columns
53–53, row 168 columns 54–55, row 168 columns 56–57, row 168 columns 58–339, row 169 columns 0–37, row 169 columns
38–39, row 169 columns 40–41, row 169 columns 42–42, row 169 columns 43–43, row 169 columns 44–44, row 169 columns
45–45, row 169 columns 46–46, row 169 columns 47–47, row 169 columns 48–48), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4363 : rowsJ2 168 169 51 52 ≤ 15307203383518 := by decide +kernel

theorem rows22250R_4364 : rowsJ2 168 169 52 53 ≤ 13529710918408 := by decide +kernel

theorem rows22250R_4365 : rowsJ2 168 169 53 54 ≤ 11874914505785 := by decide +kernel

theorem rows22250R_4366 : rowsJ2 168 169 54 56 ≤ 19258975482856 := by decide +kernel

theorem rows22250R_4367 : rowsJ2 168 169 56 58 ≤ 14029788726580 := by decide +kernel

theorem rows22250R_4368 : rowsJ2 168 169 58 340 ≤ 2696889787263223 := by decide +kernel

theorem rows22250R_4369 : rowsJ2 169 170 0 38 ≤ 19023513794753 := by decide +kernel

theorem rows22250R_4370 : rowsJ2 169 170 38 40 ≤ 15895121417096 := by decide +kernel

theorem rows22250R_4371 : rowsJ2 169 170 40 42 ≤ 21154913051037 := by decide +kernel

theorem rows22250R_4372 : rowsJ2 169 170 42 43 ≤ 12727953307523 := by decide +kernel

theorem rows22250R_4373 : rowsJ2 169 170 43 44 ≤ 14250835601938 := by decide +kernel

theorem rows22250R_4374 : rowsJ2 169 170 44 45 ≤ 15837553003719 := by decide +kernel

theorem rows22250R_4375 : rowsJ2 169 170 45 46 ≤ 17485973286368 := by decide +kernel

theorem rows22250R_4376 : rowsJ2 169 170 46 47 ≤ 19194223643426 := by decide +kernel

theorem rows22250R_4377 : rowsJ2 169 170 47 48 ≤ 20960679007353 := by decide +kernel

theorem rows22250R_4378 : rowsJ2 169 170 48 49 ≤ 20740114916190 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4363
#print axioms SieveCert.rows22250R_4378
