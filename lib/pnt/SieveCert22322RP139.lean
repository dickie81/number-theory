/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 545–547 of 561

File 139 of 143: the parts `rows22322R_545` … `rows22322R_547` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22841 tests: rows 200–202, rows 203–205, rows 206–208), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_545 : rows2 200 203 ≤ 27819117591409678 := by decide +kernel

theorem rows22322R_546 : rows2 203 206 ≤ 29125482554337519 := by decide +kernel

theorem rows22322R_547 : rows2 206 209 ≤ 29458406150171794 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_545
#print axioms SieveCert.rows22322R_547
