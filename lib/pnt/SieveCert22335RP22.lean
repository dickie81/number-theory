/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 87–90 of 549

File 22 of 140: the parts `rows22335R_87` … `rows22335R_90` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24188 tests: row 60 columns 0–34, row 60 columns 35–43, row 60 columns 44–56,
row 60 columns 57–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_87 : rowsJ2 60 61 0 35 ≤ 941912155549538 := by decide +kernel

theorem rows22335R_88 : rowsJ2 60 61 35 44 ≤ 477156851410988 := by decide +kernel

theorem rows22335R_89 : rowsJ2 60 61 44 57 ≤ 742242656659821 := by decide +kernel

theorem rows22335R_90 : rowsJ2 60 61 57 300 ≤ 157086131730842 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_87
#print axioms SieveCert.rows22335R_90
