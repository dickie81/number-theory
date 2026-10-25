/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5100–5112 of 5796

File 419 of 465: the parts `rows22250R_5100` … `rows22250R_5112` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95108 tests: row 166 columns 57–57, row 166 columns 58–58, row 166 columns
59–59, row 166 columns 60–60, row 166 columns 61–61, row 166 columns 62–62, row 166 columns 63–63, row 166 columns
64–64, row 166 columns 65–65, row 166 columns 66–66, row 166 columns 67–68, row 166 columns 69–71, row 166 columns
72–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5100 : rowsJ2 166 167 57 58 ≤ 15865115197414 := by decide +kernel

theorem rows22250R_5101 : rowsJ2 166 167 58 59 ≤ 14372093458987 := by decide +kernel

theorem rows22250R_5102 : rowsJ2 166 167 59 60 ≤ 12964287252445 := by decide +kernel

theorem rows22250R_5103 : rowsJ2 166 167 60 61 ≤ 11639268333230 := by decide +kernel

theorem rows22250R_5104 : rowsJ2 166 167 61 62 ≤ 10394772833453 := by decide +kernel

theorem rows22250R_5105 : rowsJ2 166 167 62 63 ≤ 9228693213353 := by decide +kernel

theorem rows22250R_5106 : rowsJ2 166 167 63 64 ≤ 8139070919475 := by decide +kernel

theorem rows22250R_5107 : rowsJ2 166 167 64 65 ≤ 7124089698812 := by decide +kernel

theorem rows22250R_5108 : rowsJ2 166 167 65 66 ≤ 6182069523335 := by decide +kernel

theorem rows22250R_5109 : rowsJ2 166 167 66 67 ≤ 5311461084662 := by decide +kernel

theorem rows22250R_5110 : rowsJ2 166 167 67 69 ≤ 8289747284784 := by decide +kernel

theorem rows22250R_5111 : rowsJ2 166 167 69 72 ≤ 7614876728845 := by decide +kernel

theorem rows22250R_5112 : rowsJ2 166 167 72 360 ≤ 2534530376484736 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5100
#print axioms SieveCert.rows22250R_5112
