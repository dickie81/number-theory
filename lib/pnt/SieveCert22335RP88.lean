/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 339–342 of 549

File 88 of 140: the parts `rows22335R_339` … `rows22335R_342` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25796 tests: row 104 columns 58–62, row 104 columns 63–68, row 104 columns
69–76, row 104 columns 77–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_339 : rowsJ2 104 105 58 63 ≤ 2264378938744 := by decide +kernel

theorem rows22335R_340 : rowsJ2 104 105 63 69 ≤ 0 := by decide +kernel

theorem rows22335R_341 : rowsJ2 104 105 69 77 ≤ 3290452529771 := by decide +kernel

theorem rows22335R_342 : rowsJ2 104 105 77 300 ≤ 701184259987460 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_339
#print axioms SieveCert.rows22335R_342
