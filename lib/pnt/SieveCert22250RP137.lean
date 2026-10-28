/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1567–1576 of 4715

File 137 of 351: the parts `rows22250R_1567` … `rows22250R_1576` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, work 92188 in units of a depth-4 test: row 75 columns 45–45, row 75 columns
46–46, row 75 columns 47–47, row 75 columns 48–48, row 75 columns 49–49, row 75 columns 50–50, row 75 columns 51–51,
row 75 columns 52–52, row 75 columns 53–53, row 75 columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1567 : rowsJ2 75 76 45 46 ≤ 237319602535 := by decide +kernel

theorem rows22250R_1568 : rowsJ2 75 76 46 47 ≤ 708007122206 := by decide +kernel

theorem rows22250R_1569 : rowsJ2 75 76 47 48 ≤ 1405992321297 := by decide +kernel

theorem rows22250R_1570 : rowsJ2 75 76 48 49 ≤ 1974658521914 := by decide +kernel

theorem rows22250R_1571 : rowsJ2 75 76 49 50 ≤ 2380508610512 := by decide +kernel

theorem rows22250R_1572 : rowsJ2 75 76 50 51 ≤ 2797483615773 := by decide +kernel

theorem rows22250R_1573 : rowsJ2 75 76 51 52 ≤ 3172082101934 := by decide +kernel

theorem rows22250R_1574 : rowsJ2 75 76 52 53 ≤ 3302465577683 := by decide +kernel

theorem rows22250R_1575 : rowsJ2 75 76 53 54 ≤ 3016699183504 := by decide +kernel

theorem rows22250R_1576 : rowsJ2 75 76 54 55 ≤ 2724344948091 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1567
#print axioms SieveCert.rows22250R_1576
