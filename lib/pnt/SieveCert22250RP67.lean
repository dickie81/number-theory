/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 621–628 of 5796

File 67 of 465: the parts `rows22250R_621` … `rows22250R_628` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 96132 tests: row 52 columns 39–39, row 52 columns 40–40, row 52 columns
41–41, row 52 columns 42–42, row 52 columns 43–43, row 52 columns 44–44, row 52 columns 45–45, row 52 columns
46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_621 : rowsJ2 52 53 39 40 ≤ 1825236162 := by decide +kernel

theorem rows22250R_622 : rowsJ2 52 53 40 41 ≤ 908528306 := by decide +kernel

theorem rows22250R_623 : rowsJ2 52 53 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_624 : rowsJ2 52 53 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_625 : rowsJ2 52 53 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_626 : rowsJ2 52 53 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_627 : rowsJ2 52 53 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_628 : rowsJ2 52 53 46 47 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_621
#print axioms SieveCert.rows22250R_628
