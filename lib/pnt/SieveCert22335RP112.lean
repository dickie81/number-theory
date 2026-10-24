/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 431–434 of 549

File 112 of 140: the parts `rows22335R_431` … `rows22335R_434` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25765 tests: row 123 columns 54–62, row 123 columns 63–299, row 124 columns
0–46, row 124 columns 47–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_431 : rowsJ2 123 124 54 63 ≤ 34336661745875 := by decide +kernel

theorem rows22335R_432 : rowsJ2 123 124 63 300 ≤ 1062367187471602 := by decide +kernel

theorem rows22335R_433 : rowsJ2 124 125 0 47 ≤ 164163796555013 := by decide +kernel

theorem rows22335R_434 : rowsJ2 124 125 47 54 ≤ 85517482316224 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_431
#print axioms SieveCert.rows22335R_434
