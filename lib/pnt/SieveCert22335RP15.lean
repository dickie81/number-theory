/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 59–62 of 549

File 15 of 140: the parts `rows22335R_59` … `rows22335R_62` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24372 tests: row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–51,
row 53 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_59 : rowsJ2 53 54 0 35 ≤ 1377472019647424 := by decide +kernel

theorem rows22335R_60 : rowsJ2 53 54 35 44 ≤ 372184419869940 := by decide +kernel

theorem rows22335R_61 : rowsJ2 53 54 44 52 ≤ 598575868882281 := by decide +kernel

theorem rows22335R_62 : rowsJ2 53 54 52 300 ≤ 132433196079458 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_59
#print axioms SieveCert.rows22335R_62
