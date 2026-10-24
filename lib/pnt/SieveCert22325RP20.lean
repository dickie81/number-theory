/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 79–82 of 561

File 20 of 142: the parts `rows22325R_79` … `rows22325R_82` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24726 tests: row 58 columns 0–34, row 58 columns 35–43, row 58 columns 44–54,
row 58 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_79 : rowsJ2 58 59 0 35 ≤ 1055884983481676 := by decide +kernel

theorem rows22325R_80 : rowsJ2 58 59 35 44 ≤ 446162594244232 := by decide +kernel

theorem rows22325R_81 : rowsJ2 58 59 44 55 ≤ 696586449482707 := by decide +kernel

theorem rows22325R_82 : rowsJ2 58 59 55 300 ≤ 190262961675420 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_79
#print axioms SieveCert.rows22325R_82
