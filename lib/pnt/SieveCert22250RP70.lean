/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 731–742 of 4715

File 70 of 351: the parts `rows22250R_731` … `rows22250R_742` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 98638 in units of a depth-4 test: row 56 columns 30–30, row 56 columns
31–31, row 56 columns 32–32, row 56 columns 33–33, row 56 columns 34–34, row 56 columns 35–35, row 56 columns 36–36,
row 56 columns 37–37, row 56 columns 38–38, row 56 columns 39–39, row 56 columns 40–40, row 56 columns 41–41), each
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

theorem rows22250R_731 : rowsJ2 56 57 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_732 : rowsJ2 56 57 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_733 : rowsJ2 56 57 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_734 : rowsJ2 56 57 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_735 : rowsJ2 56 57 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_736 : rowsJ2 56 57 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_737 : rowsJ2 56 57 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_738 : rowsJ2 56 57 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_739 : rowsJ2 56 57 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_740 : rowsJ2 56 57 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_741 : rowsJ2 56 57 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_742 : rowsJ2 56 57 41 42 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_731
#print axioms SieveCert.rows22250R_742
