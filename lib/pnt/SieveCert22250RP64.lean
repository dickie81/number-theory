/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 661–670 of 4715

File 64 of 351: the parts `rows22250R_661` … `rows22250R_670` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 95856 tests: row 54 columns 30–30, row 54 columns 31–31, row 54 columns
32–32, row 54 columns 33–33, row 54 columns 34–34, row 54 columns 35–35, row 54 columns 36–36, row 54 columns 37–37,
row 54 columns 38–38, row 54 columns 39–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_661 : rowsJ2 54 55 30 31 ≤ 10181641539 := by decide +kernel

theorem rows22250R_662 : rowsJ2 54 55 31 32 ≤ 4468481118 := by decide +kernel

theorem rows22250R_663 : rowsJ2 54 55 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_664 : rowsJ2 54 55 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_665 : rowsJ2 54 55 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_666 : rowsJ2 54 55 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_667 : rowsJ2 54 55 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_668 : rowsJ2 54 55 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_669 : rowsJ2 54 55 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_670 : rowsJ2 54 55 39 40 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_661
#print axioms SieveCert.rows22250R_670
