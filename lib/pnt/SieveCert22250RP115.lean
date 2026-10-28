/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1274–1290 of 4715

File 115 of 351: the parts `rows22250R_1274` … `rows22250R_1290` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 95712 in units of a depth-4 test: row 69 columns 22–22, row 69 columns
23–23, row 69 columns 24–24, row 69 columns 25–25, row 69 columns 26–26, row 69 columns 27–27, row 69 columns 28–28,
row 69 columns 29–29, row 69 columns 30–30, row 69 columns 31–31, row 69 columns 32–32, row 69 columns 33–34, row 69
columns 35–36, row 69 columns 37–38, row 69 columns 39–40, row 69 columns 41–42, row 69 columns 43–43), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1274 : rowsJ2 69 70 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1275 : rowsJ2 69 70 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1276 : rowsJ2 69 70 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1277 : rowsJ2 69 70 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1278 : rowsJ2 69 70 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1279 : rowsJ2 69 70 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1280 : rowsJ2 69 70 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1281 : rowsJ2 69 70 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1282 : rowsJ2 69 70 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1283 : rowsJ2 69 70 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1284 : rowsJ2 69 70 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1285 : rowsJ2 69 70 33 35 ≤ 0 := by decide +kernel

theorem rows22250R_1286 : rowsJ2 69 70 35 37 ≤ 0 := by decide +kernel

theorem rows22250R_1287 : rowsJ2 69 70 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1288 : rowsJ2 69 70 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1289 : rowsJ2 69 70 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1290 : rowsJ2 69 70 43 44 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1274
#print axioms SieveCert.rows22250R_1290
