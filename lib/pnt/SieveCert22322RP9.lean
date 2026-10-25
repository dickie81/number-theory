/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 36–39 of 561

File 9 of 143: the parts `rows22322R_36` … `rows22322R_39` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26194 tests: row 46 columns 0–34, row 46 columns 35–43, row 46 columns
44–299, row 47 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_36 : rowsJ2 46 47 0 35 ≤ 1968803314257557 := by decide +kernel

theorem rows22322R_37 : rowsJ2 46 47 35 44 ≤ 406330479143655 := by decide +kernel

theorem rows22322R_38 : rowsJ2 46 47 44 300 ≤ 200084114854395 := by decide +kernel

theorem rows22322R_39 : rowsJ2 47 48 0 35 ≤ 1891002392287728 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_36
#print axioms SieveCert.rows22322R_39
