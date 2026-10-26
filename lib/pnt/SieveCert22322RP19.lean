/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 75–78 of 561

File 19 of 143: the parts `rows22322R_75` … `rows22322R_78` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24875 tests: row 57 columns 0–34, row 57 columns 35–43, row 57 columns 44–53,
row 57 columns 54–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_75 : rowsJ2 57 58 0 35 ≤ 1179091544167254 := by decide +kernel

theorem rows22322R_76 : rowsJ2 57 58 35 44 ≤ 437783193071713 := by decide +kernel

theorem rows22322R_77 : rowsJ2 57 58 44 54 ≤ 665921195486972 := by decide +kernel

theorem rows22322R_78 : rowsJ2 57 58 54 300 ≤ 207951278016971 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_75
#print axioms SieveCert.rows22322R_78
