/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1472–1478 of 5796

File 149 of 465: the parts `rows22250R_1472` … `rows22250R_1478` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 98125 tests: row 72 columns 57–57, row 72 columns 58–58, row 72 columns
59–59, row 72 columns 60–60, row 72 columns 61–61, row 72 columns 62–62, row 72 columns 63–63), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1472 : rowsJ2 72 73 57 58 ≤ 5885347636492 := by decide +kernel

theorem rows22250R_1473 : rowsJ2 72 73 58 59 ≤ 6291141278513 := by decide +kernel

theorem rows22250R_1474 : rowsJ2 72 73 59 60 ≤ 6615704296084 := by decide +kernel

theorem rows22250R_1475 : rowsJ2 72 73 60 61 ≤ 6297245559523 := by decide +kernel

theorem rows22250R_1476 : rowsJ2 72 73 61 62 ≤ 5930463121949 := by decide +kernel

theorem rows22250R_1477 : rowsJ2 72 73 62 63 ≤ 5608810439785 := by decide +kernel

theorem rows22250R_1478 : rowsJ2 72 73 63 64 ≤ 5237810507292 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1472
#print axioms SieveCert.rows22250R_1478
