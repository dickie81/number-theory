/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 144–147 of 561

File 38 of 142: the parts `rows22325R_144` … `rows22325R_147` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28710 tests: row 75 columns 0–34, row 75 columns 35–59, row 75 columns 60–67,
row 75 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22325R_144 : rowsJ2 75 76 0 35 ≤ 529696267971780 := by decide +kernel

theorem rows22325R_145 : rowsJ2 75 76 35 60 ≤ 843247624767796 := by decide +kernel

theorem rows22325R_146 : rowsJ2 75 76 60 68 ≤ 42734536909657 := by decide +kernel

theorem rows22325R_147 : rowsJ2 75 76 68 72 ≤ 13356265931958 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_144
#print axioms SieveCert.rows22325R_147
