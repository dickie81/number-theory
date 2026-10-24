/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 95–97 of 549

File 24 of 140: the parts `rows22335R_95` … `rows22335R_97` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23352 tests: row 62 columns 0–34, row 62 columns 35–44, row 62 columns
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

theorem rows22335R_95 : rowsJ2 62 63 0 35 ≤ 840826078900246 := by decide +kernel

theorem rows22335R_96 : rowsJ2 62 63 35 45 ≤ 569634979449070 := by decide +kernel

theorem rows22335R_97 : rowsJ2 62 63 45 300 ≤ 823132823321453 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_95
#print axioms SieveCert.rows22335R_97
