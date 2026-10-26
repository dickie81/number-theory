/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 95–97 of 561

File 24 of 143: the parts `rows22322R_95` … `rows22322R_97` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 23352 tests: row 62 columns 0–34, row 62 columns 35–44, row 62 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_95 : rowsJ2 62 63 0 35 ≤ 896720406088055 := by decide +kernel

theorem rows22322R_96 : rowsJ2 62 63 35 45 ≤ 572711605144480 := by decide +kernel

theorem rows22322R_97 : rowsJ2 62 63 45 300 ≤ 827028544352493 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_95
#print axioms SieveCert.rows22322R_97
