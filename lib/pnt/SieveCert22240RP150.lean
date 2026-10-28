/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1617–1630 of 5066

File 150 of 387: the parts `rows22240R_1617` … `rows22240R_1630` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98492 in units of a depth-4 test: row 75 columns 34–35, row 75 columns
36–37, row 75 columns 38–39, row 75 columns 40–41, row 75 columns 42–42, row 75 columns 43–43, row 75 columns 44–44,
row 75 columns 45–45, row 75 columns 46–46, row 75 columns 47–47, row 75 columns 48–48, row 75 columns 49–49, row 75
columns 50–50, row 75 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1617 : rowsJ2 75 76 34 36 ≤ 0 := by decide +kernel

theorem rows22240R_1618 : rowsJ2 75 76 36 38 ≤ 0 := by decide +kernel

theorem rows22240R_1619 : rowsJ2 75 76 38 40 ≤ 0 := by decide +kernel

theorem rows22240R_1620 : rowsJ2 75 76 40 42 ≤ 0 := by decide +kernel

theorem rows22240R_1621 : rowsJ2 75 76 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1622 : rowsJ2 75 76 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1623 : rowsJ2 75 76 44 45 ≤ 61335596883 := by decide +kernel

theorem rows22240R_1624 : rowsJ2 75 76 45 46 ≤ 179372402647 := by decide +kernel

theorem rows22240R_1625 : rowsJ2 75 76 46 47 ≤ 349801321622 := by decide +kernel

theorem rows22240R_1626 : rowsJ2 75 76 47 48 ≤ 746854917223 := by decide +kernel

theorem rows22240R_1627 : rowsJ2 75 76 48 49 ≤ 1426866135993 := by decide +kernel

theorem rows22240R_1628 : rowsJ2 75 76 49 50 ≤ 2100402672044 := by decide +kernel

theorem rows22240R_1629 : rowsJ2 75 76 50 51 ≤ 2554230072380 := by decide +kernel

theorem rows22240R_1630 : rowsJ2 75 76 51 52 ≤ 2959157542062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1617
#print axioms SieveCert.rows22240R_1630
