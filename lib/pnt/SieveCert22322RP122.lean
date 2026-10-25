/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 470–473 of 561

File 122 of 143: the parts `rows22322R_470` … `rows22322R_473` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25541 tests: row 131 columns 52–299, row 132 columns 0–43, row 132 columns
44–51, row 132 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_470 : rowsJ2 131 132 52 300 ≤ 2397180850755207 := by decide +kernel

theorem rows22322R_471 : rowsJ2 132 133 0 44 ≤ 130257279569240 := by decide +kernel

theorem rows22322R_472 : rowsJ2 132 133 44 52 ≤ 110892550591294 := by decide +kernel

theorem rows22322R_473 : rowsJ2 132 133 52 300 ≤ 2534681999809488 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_470
#print axioms SieveCert.rows22322R_473
