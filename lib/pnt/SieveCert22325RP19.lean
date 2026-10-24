/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 75–78 of 561

File 19 of 142: the parts `rows22325R_75` … `rows22325R_78` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24875 tests: row 57 columns 0–34, row 57 columns 35–43, row 57 columns 44–53,
row 57 columns 54–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_75 : rowsJ2 57 58 0 35 ≤ 1116155643165791 := by decide +kernel

theorem rows22325R_76 : rowsJ2 57 58 35 44 ≤ 430614802172811 := by decide +kernel

theorem rows22325R_77 : rowsJ2 57 58 44 54 ≤ 663566547047382 := by decide +kernel

theorem rows22325R_78 : rowsJ2 57 58 54 300 ≤ 207197168756070 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_75
#print axioms SieveCert.rows22325R_78
