/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 107–109 of 549

File 28 of 140: the parts `rows22335R_107` … `rows22335R_109` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23266 tests: row 66 columns 0–34, row 66 columns 35–45, row 66 columns
46–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_107 : rowsJ2 66 67 0 35 ≤ 679993863049662 := by decide +kernel

theorem rows22335R_108 : rowsJ2 66 67 35 46 ≤ 646994855994744 := by decide +kernel

theorem rows22335R_109 : rowsJ2 66 67 46 300 ≤ 692087426974881 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_107
#print axioms SieveCert.rows22335R_109
