/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 28–30 of 561

File 7 of 143: the parts `rows22322R_28` … `rows22322R_30` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22950 tests: row 43 columns 0–34, row 43 columns 35–299, row 44 columns
0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_28 : rowsJ2 43 44 0 35 ≤ 2206425272185812 := by decide +kernel

theorem rows22322R_29 : rowsJ2 43 44 35 300 ≤ 455163878873559 := by decide +kernel

theorem rows22322R_30 : rowsJ2 44 45 0 35 ≤ 2126566755677628 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_28
#print axioms SieveCert.rows22322R_30
