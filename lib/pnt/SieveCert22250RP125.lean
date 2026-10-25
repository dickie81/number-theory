/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1206–1220 of 5796

File 125 of 465: the parts `rows22250R_1206` … `rows22250R_1220` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96472 tests: row 67 columns 39–39, row 67 columns 40–40, row 67 columns
41–41, row 67 columns 42–42, row 67 columns 43–43, row 67 columns 44–44, row 67 columns 45–45, row 67 columns 46–46,
row 67 columns 47–47, row 67 columns 48–48, row 67 columns 49–49, row 67 columns 50–50, row 67 columns 51–51, row 67
columns 52–52, row 67 columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1206 : rowsJ2 67 68 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1207 : rowsJ2 67 68 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1208 : rowsJ2 67 68 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1209 : rowsJ2 67 68 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1210 : rowsJ2 67 68 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1211 : rowsJ2 67 68 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1212 : rowsJ2 67 68 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1213 : rowsJ2 67 68 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1214 : rowsJ2 67 68 47 48 ≤ 105734552201 := by decide +kernel

theorem rows22250R_1215 : rowsJ2 67 68 48 49 ≤ 473885234340 := by decide +kernel

theorem rows22250R_1216 : rowsJ2 67 68 49 50 ≤ 882436213127 := by decide +kernel

theorem rows22250R_1217 : rowsJ2 67 68 50 51 ≤ 1327210150262 := by decide +kernel

theorem rows22250R_1218 : rowsJ2 67 68 51 52 ≤ 1910514641618 := by decide +kernel

theorem rows22250R_1219 : rowsJ2 67 68 52 53 ≤ 2738165918315 := by decide +kernel

theorem rows22250R_1220 : rowsJ2 67 68 53 54 ≤ 3587212877566 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1206
#print axioms SieveCert.rows22250R_1220
