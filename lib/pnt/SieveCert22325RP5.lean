/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 20–23 of 561

File 5 of 142: the parts `rows22325R_20` … `rows22325R_23` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23821 tests: row 39 columns 0–34, row 39 columns 35–299, row 40 columns 0–34,
row 40 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_20 : rowsJ2 39 40 0 35 ≤ 2464940941577983 := by decide +kernel

theorem rows22325R_21 : rowsJ2 39 40 35 300 ≤ 298372105872488 := by decide +kernel

theorem rows22325R_22 : rowsJ2 40 41 0 35 ≤ 2383201855063775 := by decide +kernel

theorem rows22325R_23 : rowsJ2 40 41 35 300 ≤ 330528220777912 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_20
#print axioms SieveCert.rows22325R_23
