/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 867–870 of 1732

File 217 of 430: the parts `rows22310R_867` … `rows22310R_870` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27600 tests: row 125 columns 96–98, row 125 columns 99–101, row 125 columns
102–104, row 125 columns 105–107), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_867 : rowsJ2 125 126 96 99 ≤ 0 := by decide +kernel

theorem rows22310R_868 : rowsJ2 125 126 99 102 ≤ 189582285752 := by decide +kernel

theorem rows22310R_869 : rowsJ2 125 126 102 105 ≤ 2137806467308 := by decide +kernel

theorem rows22310R_870 : rowsJ2 125 126 105 108 ≤ 5314771624287 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_867
#print axioms SieveCert.rows22310R_870
