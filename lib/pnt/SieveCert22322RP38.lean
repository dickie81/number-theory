/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 144–147 of 561

File 38 of 143: the parts `rows22322R_144` … `rows22322R_147` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28710 tests: row 75 columns 0–34, row 75 columns 35–59, row 75 columns 60–67,
row 75 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_144 : rowsJ2 75 76 0 35 ≤ 557254836063306 := by decide +kernel

theorem rows22322R_145 : rowsJ2 75 76 35 60 ≤ 846443794889576 := by decide +kernel

theorem rows22322R_146 : rowsJ2 75 76 60 68 ≤ 42909056379346 := by decide +kernel

theorem rows22322R_147 : rowsJ2 75 76 68 72 ≤ 13387579371598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_144
#print axioms SieveCert.rows22322R_147
