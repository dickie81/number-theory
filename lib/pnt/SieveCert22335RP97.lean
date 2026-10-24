/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 372–375 of 549

File 97 of 140: the parts `rows22335R_372` … `rows22335R_375` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28418 tests: row 110 columns 63–70, row 110 columns 71–299, row 111 columns
0–50, row 111 columns 51–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_372 : rowsJ2 110 111 63 71 ≤ 2289101601258 := by decide +kernel

theorem rows22335R_373 : rowsJ2 110 111 71 300 ≤ 332219820620359 := by decide +kernel

theorem rows22335R_374 : rowsJ2 111 112 0 51 ≤ 296629731728947 := by decide +kernel

theorem rows22335R_375 : rowsJ2 111 112 51 57 ≤ 44596919483042 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_372
#print axioms SieveCert.rows22335R_375
