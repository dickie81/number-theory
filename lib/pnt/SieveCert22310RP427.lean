/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1716–1719 of 1732

File 427 of 430: the parts `rows22310R_1716` … `rows22310R_1719` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27518 tests: rows 306–307, rows 308–309, rows 310–311, rows 312–313), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1716 : rows2 306 308 ≤ 15530695731045984 := by decide +kernel

theorem rows22310R_1717 : rows2 308 310 ≤ 15589272542842752 := by decide +kernel

theorem rows22310R_1718 : rows2 310 312 ≤ 15645807687610954 := by decide +kernel

theorem rows22310R_1719 : rows2 312 314 ≤ 15694711602758651 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1716
#print axioms SieveCert.rows22310R_1719
