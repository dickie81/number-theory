/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 155–158 of 561

File 41 of 142: the parts `rows22325R_155` … `rows22325R_158` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29053 tests: row 77 columns 0–34, row 77 columns 35–60, row 77 columns 61–67,
row 77 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_155 : rowsJ2 77 78 0 35 ≤ 522706273091718 := by decide +kernel

theorem rows22325R_156 : rowsJ2 77 78 35 61 ≤ 755416081169753 := by decide +kernel

theorem rows22325R_157 : rowsJ2 77 78 61 68 ≤ 18680391245562 := by decide +kernel

theorem rows22325R_158 : rowsJ2 77 78 68 72 ≤ 12816157849579 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_155
#print axioms SieveCert.rows22325R_158
