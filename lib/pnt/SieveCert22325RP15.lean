/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 59–62 of 561

File 15 of 142: the parts `rows22325R_59` … `rows22325R_62` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24372 tests: row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–51,
row 53 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_59 : rowsJ2 53 54 0 35 ≤ 1379255973550121 := by decide +kernel

theorem rows22325R_60 : rowsJ2 53 54 35 44 ≤ 372560739703956 := by decide +kernel

theorem rows22325R_61 : rowsJ2 53 54 44 52 ≤ 599173123319913 := by decide +kernel

theorem rows22325R_62 : rowsJ2 53 54 52 300 ≤ 132567175938281 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_59
#print axioms SieveCert.rows22325R_62
