/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1511–1525 of 4715

File 133 of 351: the parts `rows22250R_1511` … `rows22250R_1525` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 94043 in units of a depth-4 test: row 74 columns 26–26, row 74 columns
27–28, row 74 columns 29–30, row 74 columns 31–32, row 74 columns 33–35, row 74 columns 36–38, row 74 columns 39–40,
row 74 columns 41–41, row 74 columns 42–42, row 74 columns 43–43, row 74 columns 44–44, row 74 columns 45–45, row 74
columns 46–46, row 74 columns 47–47, row 74 columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1511 : rowsJ2 74 75 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1512 : rowsJ2 74 75 27 29 ≤ 0 := by decide +kernel

theorem rows22250R_1513 : rowsJ2 74 75 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_1514 : rowsJ2 74 75 31 33 ≤ 0 := by decide +kernel

theorem rows22250R_1515 : rowsJ2 74 75 33 36 ≤ 0 := by decide +kernel

theorem rows22250R_1516 : rowsJ2 74 75 36 39 ≤ 0 := by decide +kernel

theorem rows22250R_1517 : rowsJ2 74 75 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1518 : rowsJ2 74 75 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1519 : rowsJ2 74 75 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1520 : rowsJ2 74 75 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1521 : rowsJ2 74 75 44 45 ≤ 60963122941 := by decide +kernel

theorem rows22250R_1522 : rowsJ2 74 75 45 46 ≤ 239280400632 := by decide +kernel

theorem rows22250R_1523 : rowsJ2 74 75 46 47 ≤ 713856866617 := by decide +kernel

theorem rows22250R_1524 : rowsJ2 74 75 47 48 ≤ 1417609006308 := by decide +kernel

theorem rows22250R_1525 : rowsJ2 74 75 48 49 ≤ 2043400384175 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1511
#print axioms SieveCert.rows22250R_1525
