/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 98–100 of 549

File 25 of 140: the parts `rows22335R_98` … `rows22335R_100` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22979 tests: row 63 columns 0–34, row 63 columns 35–44, row 63 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_98 : rowsJ2 63 64 0 35 ≤ 795055765638035 := by decide +kernel

theorem rows22335R_99 : rowsJ2 63 64 35 45 ≤ 579753782668053 := by decide +kernel

theorem rows22335R_100 : rowsJ2 63 64 45 300 ≤ 811520922385333 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_98
#print axioms SieveCert.rows22335R_100
