/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1720–1723 of 1732

File 428 of 430: the parts `rows22310R_1720` … `rows22310R_1723` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28224 tests: rows 314–315, rows 316–377, rows 378–380, rows 381–383), each a
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

theorem rows22310R_1720 : rows2 314 316 ≤ 15746068948549373 := by decide +kernel

theorem rows22310R_1721 : rows2 316 378 ≤ 15794378572543540 := by decide +kernel

theorem rows22310R_1722 : rows2 378 381 ≤ 25355056676943366 := by decide +kernel

theorem rows22310R_1723 : rows2 381 384 ≤ 26287173345610774 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1720
#print axioms SieveCert.rows22310R_1723
