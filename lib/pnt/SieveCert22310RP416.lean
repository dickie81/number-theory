/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1659–1664 of 1732

File 416 of 430: the parts `rows22310R_1659` … `rows22310R_1664` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (6 parts, 27406 tests: rows 231–231, rows 232–232, rows 233–233, rows 234–234, rows
235–235, rows 236–236), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1659 : rows2 231 232 ≤ 4200004393649121 := by decide +kernel

theorem rows22310R_1660 : rows2 232 233 ≤ 4282702434033137 := by decide +kernel

theorem rows22310R_1661 : rows2 233 234 ≤ 4366007314549113 := by decide +kernel

theorem rows22310R_1662 : rows2 234 235 ≤ 4449899713806690 := by decide +kernel

theorem rows22310R_1663 : rows2 235 236 ≤ 4534358188633016 := by decide +kernel

theorem rows22310R_1664 : rows2 236 237 ≤ 4619312068646656 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1659
#print axioms SieveCert.rows22310R_1664
