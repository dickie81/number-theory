/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3428–3441 of 4715

File 265 of 351: the parts `rows22250R_3428` … `rows22250R_3441` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 95093 in units of a depth-4 test: row 129 columns 30–49, row 129
columns 50–55, row 129 columns 56–57, row 129 columns 58–58, row 129 columns 59–59, row 129 columns 60–60, row 129
columns 61–61, row 129 columns 62–62, row 129 columns 63–63, row 129 columns 64–64, row 129 columns 65–65, row 129
columns 66–66, row 129 columns 67–67, row 129 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3428 : rowsJ2 129 130 30 50 ≤ 4002426551398 := by decide +kernel

theorem rows22250R_3429 : rowsJ2 129 130 50 56 ≤ 6406217536329 := by decide +kernel

theorem rows22250R_3430 : rowsJ2 129 130 56 58 ≤ 5551047093864 := by decide +kernel

theorem rows22250R_3431 : rowsJ2 129 130 58 59 ≤ 3631271183687 := by decide +kernel

theorem rows22250R_3432 : rowsJ2 129 130 59 60 ≤ 4258724178702 := by decide +kernel

theorem rows22250R_3433 : rowsJ2 129 130 60 61 ≤ 4904772785501 := by decide +kernel

theorem rows22250R_3434 : rowsJ2 129 130 61 62 ≤ 5502786813362 := by decide +kernel

theorem rows22250R_3435 : rowsJ2 129 130 62 63 ≤ 6030332267419 := by decide +kernel

theorem rows22250R_3436 : rowsJ2 129 130 63 64 ≤ 6509137998924 := by decide +kernel

theorem rows22250R_3437 : rowsJ2 129 130 64 65 ≤ 6916302929702 := by decide +kernel

theorem rows22250R_3438 : rowsJ2 129 130 65 66 ≤ 7273522362436 := by decide +kernel

theorem rows22250R_3439 : rowsJ2 129 130 66 67 ≤ 7557388080598 := by decide +kernel

theorem rows22250R_3440 : rowsJ2 129 130 67 68 ≤ 7789549677154 := by decide +kernel

theorem rows22250R_3441 : rowsJ2 129 130 68 69 ≤ 7430252428497 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3428
#print axioms SieveCert.rows22250R_3441
