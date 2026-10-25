/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 863–866 of 1732

File 216 of 430: the parts `rows22310R_863` … `rows22310R_866` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25047 tests: row 125 columns 87–88, row 125 columns 89–90, row 125 columns
91–92, row 125 columns 93–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_863 : rowsJ2 125 126 87 89 ≤ 200142737144 := by decide +kernel

theorem rows22310R_864 : rowsJ2 125 126 89 91 ≤ 108840887841 := by decide +kernel

theorem rows22310R_865 : rowsJ2 125 126 91 93 ≤ 44064264039 := by decide +kernel

theorem rows22310R_866 : rowsJ2 125 126 93 96 ≤ 7428029946 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_863
#print axioms SieveCert.rows22310R_866
