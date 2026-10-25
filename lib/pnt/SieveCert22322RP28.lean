/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 107–109 of 561

File 28 of 143: the parts `rows22322R_107` … `rows22322R_109` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 23266 tests: row 66 columns 0–34, row 66 columns 35–45, row 66 columns
46–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_107 : rowsJ2 66 67 0 35 ≤ 726584128448554 := by decide +kernel

theorem rows22322R_108 : rowsJ2 66 67 35 46 ≤ 649967953935200 := by decide +kernel

theorem rows22322R_109 : rowsJ2 66 67 46 300 ≤ 695453003195705 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_107
#print axioms SieveCert.rows22322R_109
