/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 501–504 of 561

File 129 of 142: the parts `rows22325R_501` … `rows22325R_504` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25540 tests: row 143 columns 41–299, row 144 columns 0–39, row 144 columns
40–299, row 145 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_501 : rowsJ2 143 144 41 300 ≤ 2879189414805675 := by decide +kernel

theorem rows22325R_502 : rowsJ2 144 145 0 40 ≤ 160643006641126 := by decide +kernel

theorem rows22325R_503 : rowsJ2 144 145 40 300 ≤ 2889510832394407 := by decide +kernel

theorem rows22325R_504 : rowsJ2 145 146 0 40 ≤ 173067557635023 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_501
#print axioms SieveCert.rows22325R_504
