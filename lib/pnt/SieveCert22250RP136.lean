/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1550–1566 of 4715

File 136 of 351: the parts `rows22250R_1550` … `rows22250R_1566` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99275 tests: row 75 columns 0–17, row 75 columns 18–19, row 75 columns
20–21, row 75 columns 22–22, row 75 columns 23–23, row 75 columns 24–24, row 75 columns 25–26, row 75 columns 27–28,
row 75 columns 29–30, row 75 columns 31–33, row 75 columns 34–36, row 75 columns 37–38, row 75 columns 39–40, row 75
columns 41–41, row 75 columns 42–42, row 75 columns 43–43, row 75 columns 44–44), each a sum of refined costs
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

theorem rows22250R_1550 : rowsJ2 75 76 0 18 ≤ 355888356735 := by decide +kernel

theorem rows22250R_1551 : rowsJ2 75 76 18 20 ≤ 8042077627 := by decide +kernel

theorem rows22250R_1552 : rowsJ2 75 76 20 22 ≤ 13552462799 := by decide +kernel

theorem rows22250R_1553 : rowsJ2 75 76 22 23 ≤ 4242213580 := by decide +kernel

theorem rows22250R_1554 : rowsJ2 75 76 23 24 ≤ 3176925408 := by decide +kernel

theorem rows22250R_1555 : rowsJ2 75 76 24 25 ≤ 2126668967 := by decide +kernel

theorem rows22250R_1556 : rowsJ2 75 76 25 27 ≤ 1056824839 := by decide +kernel

theorem rows22250R_1557 : rowsJ2 75 76 27 29 ≤ 0 := by decide +kernel

theorem rows22250R_1558 : rowsJ2 75 76 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_1559 : rowsJ2 75 76 31 34 ≤ 0 := by decide +kernel

theorem rows22250R_1560 : rowsJ2 75 76 34 37 ≤ 0 := by decide +kernel

theorem rows22250R_1561 : rowsJ2 75 76 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1562 : rowsJ2 75 76 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1563 : rowsJ2 75 76 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1564 : rowsJ2 75 76 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1565 : rowsJ2 75 76 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1566 : rowsJ2 75 76 44 45 ≤ 60463556845 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1550
#print axioms SieveCert.rows22250R_1566
