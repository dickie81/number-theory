/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 122–125 of 561

File 32 of 142: the parts `rows22325R_122` … `rows22325R_125` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26908 tests: row 70 columns 0–34, row 70 columns 35–49, row 70 columns 50–67,
row 70 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_122 : rowsJ2 70 71 0 35 ≤ 577986597567039 := by decide +kernel

theorem rows22325R_123 : rowsJ2 70 71 35 50 ≤ 788323320816064 := by decide +kernel

theorem rows22325R_124 : rowsJ2 70 71 50 68 ≤ 376945856081338 := by decide +kernel

theorem rows22325R_125 : rowsJ2 70 71 68 300 ≤ 21302889235551 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_122
#print axioms SieveCert.rows22325R_125
