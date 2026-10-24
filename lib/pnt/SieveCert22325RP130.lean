/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 505–509 of 561

File 130 of 142: the parts `rows22325R_505` … `rows22325R_509` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 27258 tests: row 145 columns 40–299, row 146 columns 0–39, row 146 columns
40–299, row 147 columns 0–38, row 147 columns 39–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_505 : rowsJ2 145 146 40 300 ≤ 2888481301486377 := by decide +kernel

theorem rows22325R_506 : rowsJ2 146 147 0 40 ≤ 186887730421813 := by decide +kernel

theorem rows22325R_507 : rowsJ2 146 147 40 300 ≤ 2889909793845906 := by decide +kernel

theorem rows22325R_508 : rowsJ2 147 148 0 39 ≤ 176892568324470 := by decide +kernel

theorem rows22325R_509 : rowsJ2 147 148 39 300 ≤ 2906099648496208 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_505
#print axioms SieveCert.rows22325R_509
