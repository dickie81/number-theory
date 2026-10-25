/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5047–5058 of 5796

File 415 of 465: the parts `rows22250R_5047` … `rows22250R_5058` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 96173 tests: row 164 columns 56–56, row 164 columns 57–57, row 164 columns
58–58, row 164 columns 59–59, row 164 columns 60–60, row 164 columns 61–61, row 164 columns 62–62, row 164 columns
63–63, row 164 columns 64–64, row 164 columns 65–65, row 164 columns 66–66, row 164 columns 67–67), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5047 : rowsJ2 164 165 56 57 ≤ 13007608982575 := by decide +kernel

theorem rows22250R_5048 : rowsJ2 164 165 57 58 ≤ 14153759248944 := by decide +kernel

theorem rows22250R_5049 : rowsJ2 164 165 58 59 ≤ 15335451917813 := by decide +kernel

theorem rows22250R_5050 : rowsJ2 164 165 59 60 ≤ 13893576845678 := by decide +kernel

theorem rows22250R_5051 : rowsJ2 164 165 60 61 ≤ 12533738022166 := by decide +kernel

theorem rows22250R_5052 : rowsJ2 164 165 61 62 ≤ 11253636295941 := by decide +kernel

theorem rows22250R_5053 : rowsJ2 164 165 62 63 ≤ 10051127011807 := by decide +kernel

theorem rows22250R_5054 : rowsJ2 164 165 63 64 ≤ 8924212571328 := by decide +kernel

theorem rows22250R_5055 : rowsJ2 164 165 64 65 ≤ 7871035641105 := by decide +kernel

theorem rows22250R_5056 : rowsJ2 164 165 65 66 ≤ 6889872962725 := by decide +kernel

theorem rows22250R_5057 : rowsJ2 164 165 66 67 ≤ 5979129723555 := by decide +kernel

theorem rows22250R_5058 : rowsJ2 164 165 67 68 ≤ 5137334451892 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5047
#print axioms SieveCert.rows22250R_5058
