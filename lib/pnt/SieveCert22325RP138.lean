/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 544–547 of 561

File 138 of 142: the parts `rows22325R_544` … `rows22325R_547` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29593 tests: rows 197–199, rows 200–202, rows 203–205, rows 206–208), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_544 : rows2 197 200 ≤ 26260557565225337 := by decide +kernel

theorem rows22325R_545 : rows2 200 203 ≤ 27394248825964941 := by decide +kernel

theorem rows22325R_546 : rows2 203 206 ≤ 28680120227436210 := by decide +kernel

theorem rows22325R_547 : rows2 206 209 ≤ 29492365795635867 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_544
#print axioms SieveCert.rows22325R_547
