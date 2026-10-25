/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4563–4572 of 5796

File 377 of 465: the parts `rows22250R_4563` … `rows22250R_4572` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 98813 tests: row 147 columns 59–59, row 147 columns 60–60, row 147 columns
61–61, row 147 columns 62–62, row 147 columns 63–63, row 147 columns 64–64, row 147 columns 65–65, row 147 columns
66–66, row 147 columns 67–67, row 147 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4563 : rowsJ2 147 148 59 60 ≤ 5616033757644 := by decide +kernel

theorem rows22250R_4564 : rowsJ2 147 148 60 61 ≤ 6330804365575 := by decide +kernel

theorem rows22250R_4565 : rowsJ2 147 148 61 62 ≤ 7078784063183 := by decide +kernel

theorem rows22250R_4566 : rowsJ2 147 148 62 63 ≤ 7858822653573 := by decide +kernel

theorem rows22250R_4567 : rowsJ2 147 148 63 64 ≤ 8669859139208 := by decide +kernel

theorem rows22250R_4568 : rowsJ2 147 148 64 65 ≤ 9478117192387 := by decide +kernel

theorem rows22250R_4569 : rowsJ2 147 148 65 66 ≤ 10234018711755 := by decide +kernel

theorem rows22250R_4570 : rowsJ2 147 148 66 67 ≤ 10954095812300 := by decide +kernel

theorem rows22250R_4571 : rowsJ2 147 148 67 68 ≤ 10775217059139 := by decide +kernel

theorem rows22250R_4572 : rowsJ2 147 148 68 69 ≤ 9788106031370 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4563
#print axioms SieveCert.rows22250R_4572
