/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 411–414 of 549

File 107 of 140: the parts `rows22335R_411` … `rows22335R_414` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28683 tests: row 118 columns 56–63, row 118 columns 64–299, row 119 columns
0–47, row 119 columns 48–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_411 : rowsJ2 118 119 56 64 ≤ 32317888027855 := by decide +kernel

theorem rows22335R_412 : rowsJ2 118 119 64 300 ≤ 103781993355322 := by decide +kernel

theorem rows22335R_413 : rowsJ2 119 120 0 48 ≤ 197641540560911 := by decide +kernel

theorem rows22335R_414 : rowsJ2 119 120 48 55 ≤ 78809475517800 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_411
#print axioms SieveCert.rows22335R_414
