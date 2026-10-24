/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 118–121 of 549

File 31 of 140: the parts `rows22335R_118` … `rows22335R_121` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25639 tests: row 69 columns 0–34, row 69 columns 35–48, row 69 columns 49–67,
row 69 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22335R_118 : rowsJ2 69 70 0 35 ≤ 597508088582805 := by decide +kernel

theorem rows22335R_119 : rowsJ2 69 70 35 49 ≤ 766896544855645 := by decide +kernel

theorem rows22335R_120 : rowsJ2 69 70 49 68 ≤ 448698555691314 := by decide +kernel

theorem rows22335R_121 : rowsJ2 69 70 68 300 ≤ 17126469505299 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_118
#print axioms SieveCert.rows22335R_121
