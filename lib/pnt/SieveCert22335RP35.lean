/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 133–135 of 549

File 35 of 140: the parts `rows22335R_133` … `rows22335R_135` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23146 tests: row 72 columns 68–299, row 73 columns 0–34, row 73 columns
35–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_133 : rowsJ2 72 73 68 300 ≤ 25215373258923 := by decide +kernel

theorem rows22335R_134 : rowsJ2 73 74 0 35 ≤ 538191798465024 := by decide +kernel

theorem rows22335R_135 : rowsJ2 73 74 35 58 ≤ 908521446747499 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_133
#print axioms SieveCert.rows22335R_135
