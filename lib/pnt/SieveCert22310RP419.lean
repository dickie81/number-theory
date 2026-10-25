/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1672–1675 of 1732

File 419 of 430: the parts `rows22310R_1672` … `rows22310R_1675` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29811 tests: rows 251–252, rows 253–254, rows 255–256, rows 257–258), each a
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

theorem rows22310R_1672 : rows2 251 253 ≤ 11481418025922405 := by decide +kernel

theorem rows22310R_1673 : rows2 253 255 ≤ 11681066201797202 := by decide +kernel

theorem rows22310R_1674 : rows2 255 257 ≤ 11894142222602802 := by decide +kernel

theorem rows22310R_1675 : rows2 257 259 ≤ 12121109034171961 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1672
#print axioms SieveCert.rows22310R_1675
