/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 48–50 of 561

File 12 of 143: the parts `rows22322R_48` … `rows22322R_50` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22658 tests: row 50 columns 0–34, row 50 columns 35–43, row 50 columns
44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_48 : rowsJ2 50 51 0 35 ≤ 1662895884086597 := by decide +kernel

theorem rows22322R_49 : rowsJ2 50 51 35 44 ≤ 378632078676517 := by decide +kernel

theorem rows22322R_50 : rowsJ2 50 51 44 300 ≤ 542504042903214 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_48
#print axioms SieveCert.rows22322R_50
