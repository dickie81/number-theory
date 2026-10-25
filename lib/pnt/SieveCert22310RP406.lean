/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1612–1616 of 1732

File 406 of 430: the parts `rows22310R_1612` … `rows22310R_1616` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29987 tests: row 205 columns 41–47, row 205 columns 48–399, row 206 columns
0–40, row 206 columns 41–47, row 206 columns 48–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1612 : rowsJ2 205 206 41 48 ≤ 93616384816039 := by decide +kernel

theorem rows22310R_1613 : rowsJ2 205 206 48 400 ≤ 2244809818858542 := by decide +kernel

theorem rows22310R_1614 : rowsJ2 206 207 0 41 ≤ 36432904910124 := by decide +kernel

theorem rows22310R_1615 : rowsJ2 206 207 41 48 ≤ 97916546635496 := by decide +kernel

theorem rows22310R_1616 : rowsJ2 206 207 48 400 ≤ 2246403222019842 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1612
#print axioms SieveCert.rows22310R_1616
