/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1446–1462 of 5796

File 147 of 465: the parts `rows22250R_1446` … `rows22250R_1462` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 95655 tests: row 72 columns 29–29, row 72 columns 30–30, row 72 columns
31–31, row 72 columns 32–32, row 72 columns 33–33, row 72 columns 34–34, row 72 columns 35–35, row 72 columns 36–36,
row 72 columns 37–37, row 72 columns 38–39, row 72 columns 40–41, row 72 columns 42–42, row 72 columns 43–43, row 72
columns 44–44, row 72 columns 45–45, row 72 columns 46–46, row 72 columns 47–47), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1446 : rowsJ2 72 73 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1447 : rowsJ2 72 73 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1448 : rowsJ2 72 73 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1449 : rowsJ2 72 73 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1450 : rowsJ2 72 73 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1451 : rowsJ2 72 73 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1452 : rowsJ2 72 73 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1453 : rowsJ2 72 73 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1454 : rowsJ2 72 73 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1455 : rowsJ2 72 73 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1456 : rowsJ2 72 73 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1457 : rowsJ2 72 73 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1458 : rowsJ2 72 73 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1459 : rowsJ2 72 73 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1460 : rowsJ2 72 73 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1461 : rowsJ2 72 73 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1462 : rowsJ2 72 73 47 48 ≤ 101394008557 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1446
#print axioms SieveCert.rows22250R_1462
