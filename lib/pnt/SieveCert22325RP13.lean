/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 51–54 of 561

File 13 of 142: the parts `rows22325R_51` … `rows22325R_54` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23379 tests: row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–50,
row 51 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_51 : rowsJ2 51 52 0 35 ≤ 1521768482213221 := by decide +kernel

theorem rows22325R_52 : rowsJ2 51 52 35 44 ≤ 360491235037204 := by decide +kernel

theorem rows22325R_53 : rowsJ2 51 52 44 51 ≤ 537692838055931 := by decide +kernel

theorem rows22325R_54 : rowsJ2 51 52 51 300 ≤ 73188439362670 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_51
#print axioms SieveCert.rows22325R_54
