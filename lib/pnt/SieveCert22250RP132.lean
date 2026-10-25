/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1279–1288 of 5796

File 132 of 465: the parts `rows22250R_1279` … `rows22250R_1288` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 96429 tests: row 68 columns 64–64, row 68 columns 65–65, row 68 columns
66–66, row 68 columns 67–67, row 68 columns 68–359, row 69 columns 0–17, row 69 columns 18–21, row 69 columns 22–22,
row 69 columns 23–23, row 69 columns 24–24), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1279 : rowsJ2 68 69 64 65 ≤ 8283289065229 := by decide +kernel

theorem rows22250R_1280 : rowsJ2 68 69 65 66 ≤ 7812947143162 := by decide +kernel

theorem rows22250R_1281 : rowsJ2 68 69 66 67 ≤ 7388414903265 := by decide +kernel

theorem rows22250R_1282 : rowsJ2 68 69 67 68 ≤ 6968029285333 := by decide +kernel

theorem rows22250R_1283 : rowsJ2 68 69 68 360 ≤ 6593389790527 := by decide +kernel

theorem rows22250R_1284 : rowsJ2 69 70 0 18 ≤ 1283027717009 := by decide +kernel

theorem rows22250R_1285 : rowsJ2 69 70 18 22 ≤ 43552725215 := by decide +kernel

theorem rows22250R_1286 : rowsJ2 69 70 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1287 : rowsJ2 69 70 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1288 : rowsJ2 69 70 24 25 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1279
#print axioms SieveCert.rows22250R_1288
