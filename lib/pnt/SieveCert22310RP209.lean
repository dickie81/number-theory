/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 835–838 of 1732

File 209 of 430: the parts `rows22310R_835` … `rows22310R_838` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27663 tests: row 123 columns 107–109, row 123 columns 110–113, row 123
columns 114–399, row 124 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_835 : rowsJ2 123 124 107 110 ≤ 7262409262530 := by decide +kernel

theorem rows22310R_836 : rowsJ2 123 124 110 114 ≤ 17308458089795 := by decide +kernel

theorem rows22310R_837 : rowsJ2 123 124 114 400 ≤ 556786881511801 := by decide +kernel

theorem rows22310R_838 : rowsJ2 124 125 0 35 ≤ 113031548218612 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_835
#print axioms SieveCert.rows22310R_838
