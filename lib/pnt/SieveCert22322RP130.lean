/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 503–507 of 561

File 130 of 143: the parts `rows22322R_503` … `rows22322R_507` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 29018 tests: row 144 columns 40–299, row 145 columns 0–39, row 145 columns
40–299, row 146 columns 0–39, row 146 columns 40–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_503 : rowsJ2 144 145 40 300 ≤ 2966976938839821 := by decide +kernel

theorem rows22322R_504 : rowsJ2 145 146 0 40 ≤ 173626569863277 := by decide +kernel

theorem rows22322R_505 : rowsJ2 145 146 40 300 ≤ 2966006881541182 := by decide +kernel

theorem rows22322R_506 : rowsJ2 146 147 0 40 ≤ 187494535414155 := by decide +kernel

theorem rows22322R_507 : rowsJ2 146 147 40 300 ≤ 2967501023400790 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_503
#print axioms SieveCert.rows22322R_507
