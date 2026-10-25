/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1606–1618 of 4715

File 140 of 351: the parts `rows22250R_1606` … `rows22250R_1618` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97474 tests: row 76 columns 39–40, row 76 columns 41–41, row 76 columns
42–42, row 76 columns 43–43, row 76 columns 44–44, row 76 columns 45–45, row 76 columns 46–46, row 76 columns 47–47,
row 76 columns 48–48, row 76 columns 49–49, row 76 columns 50–50, row 76 columns 51–51, row 76 columns 52–52), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1606 : rowsJ2 76 77 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1607 : rowsJ2 76 77 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1608 : rowsJ2 76 77 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1609 : rowsJ2 76 77 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1610 : rowsJ2 76 77 44 45 ≤ 59972111653 := by decide +kernel

theorem rows22250R_1611 : rowsJ2 76 77 45 46 ≤ 235390679002 := by decide +kernel

theorem rows22250R_1612 : rowsJ2 76 77 46 47 ≤ 702252470737 := by decide +kernel

theorem rows22250R_1613 : rowsJ2 76 77 47 48 ≤ 1394564476117 := by decide +kernel

theorem rows22250R_1614 : rowsJ2 76 77 48 49 ≤ 1853796479833 := by decide +kernel

theorem rows22250R_1615 : rowsJ2 76 77 49 50 ≤ 2201295503311 := by decide +kernel

theorem rows22250R_1616 : rowsJ2 76 77 50 51 ≤ 2505137879509 := by decide +kernel

theorem rows22250R_1617 : rowsJ2 76 77 51 52 ≤ 2816901878102 := by decide +kernel

theorem rows22250R_1618 : rowsJ2 76 77 52 53 ≤ 2710333090081 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1606
#print axioms SieveCert.rows22250R_1618
