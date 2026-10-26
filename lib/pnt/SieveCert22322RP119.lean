/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 459–461 of 561

File 119 of 143: the parts `rows22322R_459` … `rows22322R_461` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22577 tests: row 128 columns 0–44, row 128 columns 45–52, row 128 columns
53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_459 : rowsJ2 128 129 0 45 ≤ 135668255249148 := by decide +kernel

theorem rows22322R_460 : rowsJ2 128 129 45 53 ≤ 109618644846182 := by decide +kernel

theorem rows22322R_461 : rowsJ2 128 129 53 300 ≤ 1946342029646867 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_459
#print axioms SieveCert.rows22322R_461
