/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 110–113 of 561

File 29 of 142: the parts `rows22325R_110` … `rows22325R_113` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23819 tests: row 67 columns 0–34, row 67 columns 35–46, row 67 columns 47–66,
row 67 columns 67–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_110 : rowsJ2 67 68 0 35 ≤ 649528732171856 := by decide +kernel

theorem rows22325R_111 : rowsJ2 67 68 35 47 ≤ 697429541698625 := by decide +kernel

theorem rows22325R_112 : rowsJ2 67 68 47 67 ≤ 601502538383844 := by decide +kernel

theorem rows22325R_113 : rowsJ2 67 68 67 300 ≤ 12606434040733 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_110
#print axioms SieveCert.rows22325R_113
