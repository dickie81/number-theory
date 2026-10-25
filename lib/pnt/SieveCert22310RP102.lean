/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 407–409 of 1732

File 102 of 430: the parts `rows22310R_407` … `rows22310R_409` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23129 tests: row 98 columns 0–34, row 98 columns 35–43, row 98 columns
44–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_407 : rowsJ2 98 99 0 35 ≤ 281340691374793 := by decide +kernel

theorem rows22310R_408 : rowsJ2 98 99 35 44 ≤ 84048666359635 := by decide +kernel

theorem rows22310R_409 : rowsJ2 98 99 44 51 ≤ 209180377065512 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_407
#print axioms SieveCert.rows22310R_409
