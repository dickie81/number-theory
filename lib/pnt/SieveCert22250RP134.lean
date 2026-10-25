/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1303–1317 of 5796

File 134 of 465: the parts `rows22250R_1303` … `rows22250R_1317` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94134 tests: row 69 columns 39–39, row 69 columns 40–40, row 69 columns
41–41, row 69 columns 42–42, row 69 columns 43–43, row 69 columns 44–44, row 69 columns 45–45, row 69 columns 46–46,
row 69 columns 47–47, row 69 columns 48–48, row 69 columns 49–49, row 69 columns 50–50, row 69 columns 51–51, row 69
columns 52–52, row 69 columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1303 : rowsJ2 69 70 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1304 : rowsJ2 69 70 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1305 : rowsJ2 69 70 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1306 : rowsJ2 69 70 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1307 : rowsJ2 69 70 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1308 : rowsJ2 69 70 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1309 : rowsJ2 69 70 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1310 : rowsJ2 69 70 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1311 : rowsJ2 69 70 47 48 ≤ 103954490404 := by decide +kernel

theorem rows22250R_1312 : rowsJ2 69 70 48 49 ≤ 465907284046 := by decide +kernel

theorem rows22250R_1313 : rowsJ2 69 70 49 50 ≤ 867580227470 := by decide +kernel

theorem rows22250R_1314 : rowsJ2 69 70 50 51 ≤ 1304866308674 := by decide +kernel

theorem rows22250R_1315 : rowsJ2 69 70 51 52 ≤ 1878350755216 := by decide +kernel

theorem rows22250R_1316 : rowsJ2 69 70 52 53 ≤ 2692068361344 := by decide +kernel

theorem rows22250R_1317 : rowsJ2 69 70 53 54 ≤ 3526821449536 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1303
#print axioms SieveCert.rows22250R_1317
