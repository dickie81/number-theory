/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 95–97 of 561

File 24 of 142: the parts `rows22325R_95` … `rows22325R_97` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 23352 tests: row 62 columns 0–34, row 62 columns 35–44, row 62 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_95 : rowsJ2 62 63 0 35 ≤ 841906624562350 := by decide +kernel

theorem rows22325R_96 : rowsJ2 62 63 35 45 ≤ 570206680016292 := by decide +kernel

theorem rows22325R_97 : rowsJ2 62 63 45 300 ≤ 823996714587562 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_95
#print axioms SieveCert.rows22325R_97
