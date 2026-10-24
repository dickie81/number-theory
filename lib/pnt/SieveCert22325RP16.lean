/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 63–66 of 561

File 16 of 142: the parts `rows22325R_63` … `rows22325R_66` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24660 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns 44–51,
row 54 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_63 : rowsJ2 54 55 0 35 ≤ 1310665272622147 := by decide +kernel

theorem rows22325R_64 : rowsJ2 54 55 35 44 ≤ 382900105137667 := by decide +kernel

theorem rows22325R_65 : rowsJ2 54 55 44 52 ≤ 588849050823285 := by decide +kernel

theorem rows22325R_66 : rowsJ2 54 55 52 300 ≤ 189803741225975 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_63
#print axioms SieveCert.rows22325R_66
