/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2827–2834 of 5796

File 257 of 465: the parts `rows22250R_2827` … `rows22250R_2834` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 98615 tests: row 99 columns 87–87, row 99 columns 88–88, row 99 columns
89–89, row 99 columns 90–90, row 99 columns 91–91, row 99 columns 92–92, row 99 columns 93–93, row 99 columns
94–94), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2827 : rowsJ2 99 100 87 88 ≤ 2034019420008 := by decide +kernel

theorem rows22250R_2828 : rowsJ2 99 100 88 89 ≤ 2672864376298 := by decide +kernel

theorem rows22250R_2829 : rowsJ2 99 100 89 90 ≤ 3444180463536 := by decide +kernel

theorem rows22250R_2830 : rowsJ2 99 100 90 91 ≤ 4135398717064 := by decide +kernel

theorem rows22250R_2831 : rowsJ2 99 100 91 92 ≤ 4145543562665 := by decide +kernel

theorem rows22250R_2832 : rowsJ2 99 100 92 93 ≤ 3660280117158 := by decide +kernel

theorem rows22250R_2833 : rowsJ2 99 100 93 94 ≤ 3470656630540 := by decide +kernel

theorem rows22250R_2834 : rowsJ2 99 100 94 95 ≤ 3350336993073 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2827
#print axioms SieveCert.rows22250R_2834
