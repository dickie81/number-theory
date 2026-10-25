/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4285–4299 of 4715

File 325 of 351: the parts `rows22250R_4285` … `rows22250R_4299` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98187 tests: row 164 columns 49–49, row 164 columns 50–50, row 164 columns
51–51, row 164 columns 52–52, row 164 columns 53–53, row 164 columns 54–54, row 164 columns 55–55, row 164 columns
56–56, row 164 columns 57–58, row 164 columns 59–60, row 164 columns 61–339, row 165 columns 0–38, row 165 columns
39–41, row 165 columns 42–43, row 165 columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4285 : rowsJ2 164 165 49 50 ≤ 18165017994765 := by decide +kernel

theorem rows22250R_4286 : rowsJ2 164 165 50 51 ≤ 19795618202291 := by decide +kernel

theorem rows22250R_4287 : rowsJ2 164 165 51 52 ≤ 17794424905535 := by decide +kernel

theorem rows22250R_4288 : rowsJ2 164 165 52 53 ≤ 15916881252548 := by decide +kernel

theorem rows22250R_4289 : rowsJ2 164 165 53 54 ≤ 14159055340727 := by decide +kernel

theorem rows22250R_4290 : rowsJ2 164 165 54 55 ≤ 12517306636696 := by decide +kernel

theorem rows22250R_4291 : rowsJ2 164 165 55 56 ≤ 10988270111441 := by decide +kernel

theorem rows22250R_4292 : rowsJ2 164 165 56 57 ≤ 9568841905655 := by decide +kernel

theorem rows22250R_4293 : rowsJ2 164 165 57 59 ≤ 15303791007918 := by decide +kernel

theorem rows22250R_4294 : rowsJ2 164 165 59 61 ≤ 10874411525083 := by decide +kernel

theorem rows22250R_4295 : rowsJ2 164 165 61 340 ≤ 2652647216824755 := by decide +kernel

theorem rows22250R_4296 : rowsJ2 165 166 0 39 ≤ 14593893833763 := by decide +kernel

theorem rows22250R_4297 : rowsJ2 165 166 39 42 ≤ 20326658389142 := by decide +kernel

theorem rows22250R_4298 : rowsJ2 165 166 42 44 ≤ 19507736020528 := by decide +kernel

theorem rows22250R_4299 : rowsJ2 165 166 44 45 ≤ 11742029953415 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4285
#print axioms SieveCert.rows22250R_4299
