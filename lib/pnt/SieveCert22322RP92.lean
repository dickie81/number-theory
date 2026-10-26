/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 352–355 of 561

File 92 of 143: the parts `rows22322R_352` … `rows22322R_355` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26696 tests: row 105 columns 63–68, row 105 columns 69–76, row 105 columns
77–299, row 106 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_352 : rowsJ2 105 106 63 69 ≤ 0 := by decide +kernel

theorem rows22322R_353 : rowsJ2 105 106 69 77 ≤ 1245093572256 := by decide +kernel

theorem rows22322R_354 : rowsJ2 105 106 77 300 ≤ 578810926641839 := by decide +kernel

theorem rows22322R_355 : rowsJ2 106 107 0 52 ≤ 372103168176307 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_352
#print axioms SieveCert.rows22322R_355
