/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 44–47 of 561

File 11 of 143: the parts `rows22322R_44` … `rows22322R_47` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27405 tests: row 48 columns 44–299, row 49 columns 0–34, row 49 columns
35–43, row 49 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_44 : rowsJ2 48 49 44 300 ≤ 378893232655227 := by decide +kernel

theorem rows22322R_45 : rowsJ2 49 50 0 35 ≤ 1737990155695754 := by decide +kernel

theorem rows22322R_46 : rowsJ2 49 50 35 44 ≤ 381400908690159 := by decide +kernel

theorem rows22322R_47 : rowsJ2 49 50 44 300 ≤ 465483444123205 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_44
#print axioms SieveCert.rows22322R_47
