/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 20–23 of 549

File 5 of 140: the parts `rows22335R_20` … `rows22335R_23` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23821 tests: row 39 columns 0–34, row 39 columns 35–299, row 40 columns 0–34,
row 40 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_20 : rowsJ2 39 40 0 35 ≤ 2461770135467144 := by decide +kernel

theorem rows22335R_21 : rowsJ2 39 40 35 300 ≤ 298003354067307 := by decide +kernel

theorem rows22335R_22 : rowsJ2 40 41 0 35 ≤ 2380135747980518 := by decide +kernel

theorem rows22335R_23 : rowsJ2 40 41 35 300 ≤ 330124241520179 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_20
#print axioms SieveCert.rows22335R_23
