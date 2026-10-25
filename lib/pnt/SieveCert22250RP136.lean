/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1325–1331 of 5796

File 136 of 465: the parts `rows22250R_1325` … `rows22250R_1331` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 97631 tests: row 69 columns 61–61, row 69 columns 62–62, row 69 columns
63–63, row 69 columns 64–64, row 69 columns 65–65, row 69 columns 66–66, row 69 columns 67–67), each a sum of
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

theorem rows22250R_1325 : rowsJ2 69 70 61 62 ≤ 8624175022730 := by decide +kernel

theorem rows22250R_1326 : rowsJ2 69 70 62 63 ≤ 8212227561194 := by decide +kernel

theorem rows22250R_1327 : rowsJ2 69 70 63 64 ≤ 7791436805837 := by decide +kernel

theorem rows22250R_1328 : rowsJ2 69 70 64 65 ≤ 7375074541002 := by decide +kernel

theorem rows22250R_1329 : rowsJ2 69 70 65 66 ≤ 6949245286521 := by decide +kernel

theorem rows22250R_1330 : rowsJ2 69 70 66 67 ≤ 6527556509553 := by decide +kernel

theorem rows22250R_1331 : rowsJ2 69 70 67 68 ≤ 6151607149715 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1325
#print axioms SieveCert.rows22250R_1331
