/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 194–197 of 561

File 51 of 142: the parts `rows22325R_194` … `rows22325R_197` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28642 tests: row 83 columns 0–36, row 83 columns 37–61, row 83 columns 62–66,
row 83 columns 67–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22325R_194 : rowsJ2 83 84 0 37 ≤ 591902364423208 := by decide +kernel

theorem rows22325R_195 : rowsJ2 83 84 37 62 ≤ 400663752165442 := by decide +kernel

theorem rows22325R_196 : rowsJ2 83 84 62 67 ≤ 1609135975009 := by decide +kernel

theorem rows22325R_197 : rowsJ2 83 84 67 71 ≤ 8713378650752 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_194
#print axioms SieveCert.rows22325R_197
