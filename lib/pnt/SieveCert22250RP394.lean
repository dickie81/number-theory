/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4773–4781 of 5796

File 394 of 465: the parts `rows22250R_4773` … `rows22250R_4781` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 93374 tests: row 154 columns 60–60, row 154 columns 61–61, row 154 columns
62–62, row 154 columns 63–63, row 154 columns 64–64, row 154 columns 65–65, row 154 columns 66–66, row 154 columns
67–67, row 154 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4773 : rowsJ2 154 155 60 61 ≤ 10110955052432 := by decide +kernel

theorem rows22250R_4774 : rowsJ2 154 155 61 62 ≤ 11058970752694 := by decide +kernel

theorem rows22250R_4775 : rowsJ2 154 155 62 63 ≤ 12038521747476 := by decide +kernel

theorem rows22250R_4776 : rowsJ2 154 155 63 64 ≤ 13048766694235 := by decide +kernel

theorem rows22250R_4777 : rowsJ2 154 155 64 65 ≤ 11826946093822 := by decide +kernel

theorem rows22250R_4778 : rowsJ2 154 155 65 66 ≤ 10673636543041 := by decide +kernel

theorem rows22250R_4779 : rowsJ2 154 155 66 67 ≤ 9587065685441 := by decide +kernel

theorem rows22250R_4780 : rowsJ2 154 155 67 68 ≤ 8565576178140 := by decide +kernel

theorem rows22250R_4781 : rowsJ2 154 155 68 69 ≤ 7607620581444 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4773
#print axioms SieveCert.rows22250R_4781
