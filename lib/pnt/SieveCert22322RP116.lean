/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 447–450 of 561

File 116 of 143: the parts `rows22322R_447` … `rows22322R_450` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24779 tests: row 125 columns 0–45, row 125 columns 46–52, row 125 columns
53–61, row 125 columns 62–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_447 : rowsJ2 125 126 0 46 ≤ 151150674070371 := by decide +kernel

theorem rows22322R_448 : rowsJ2 125 126 46 53 ≤ 96024741733702 := by decide +kernel

theorem rows22322R_449 : rowsJ2 125 126 53 62 ≤ 43588717731629 := by decide +kernel

theorem rows22322R_450 : rowsJ2 125 126 62 300 ≤ 1421973297674554 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_447
#print axioms SieveCert.rows22322R_450
