/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 508–511 of 549

File 130 of 140: the parts `rows22335R_508` … `rows22335R_511` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23324 tests: row 153 columns 0–99, row 153 columns 100–299, rows 154–154,
rows 155–155), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_508 : rowsJ2 153 154 0 100 ≤ 1827351776965475 := by decide +kernel

theorem rows22335R_509 : rowsJ2 153 154 100 300 ≤ 1344862190047602 := by decide +kernel

theorem rows22335R_510 : rows2 154 155 ≤ 3188805717589390 := by decide +kernel

theorem rows22335R_511 : rows2 155 156 ≤ 3207730447426455 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_508
#print axioms SieveCert.rows22335R_511
