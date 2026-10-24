/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 209–212 of 561

File 55 of 142: the parts `rows22325R_209` … `rows22325R_212` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28000 tests: row 85 columns 39–61, row 85 columns 62–66, row 85 columns
67–70, row 85 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_209 : rowsJ2 85 86 39 62 ≤ 263052235704817 := by decide +kernel

theorem rows22325R_210 : rowsJ2 85 86 62 67 ≤ 1584899174662 := by decide +kernel

theorem rows22325R_211 : rowsJ2 85 86 67 71 ≤ 7208421605004 := by decide +kernel

theorem rows22325R_212 : rowsJ2 85 86 71 75 ≤ 5817380452799 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_209
#print axioms SieveCert.rows22325R_212
