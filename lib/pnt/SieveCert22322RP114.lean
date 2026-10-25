/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 438–441 of 561

File 114 of 143: the parts `rows22322R_438` … `rows22322R_441` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27806 tests: row 122 columns 62–299, row 123 columns 0–46, row 123 columns
47–53, row 123 columns 54–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_438 : rowsJ2 122 123 62 300 ≤ 882495458282490 := by decide +kernel

theorem rows22322R_439 : rowsJ2 123 124 0 47 ≤ 168232690114144 := by decide +kernel

theorem rows22322R_440 : rowsJ2 123 124 47 54 ≤ 91836134753982 := by decide +kernel

theorem rows22322R_441 : rowsJ2 123 124 54 63 ≤ 42039729289835 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_438
#print axioms SieveCert.rows22322R_441
