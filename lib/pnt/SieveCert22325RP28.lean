/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 107–109 of 561

File 28 of 142: the parts `rows22325R_107` … `rows22325R_109` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 23266 tests: row 66 columns 0–34, row 66 columns 35–45, row 66 columns
46–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_107 : rowsJ2 66 67 0 35 ≤ 680853578305168 := by decide +kernel

theorem rows22325R_108 : rowsJ2 66 67 35 46 ≤ 647654198590001 := by decide +kernel

theorem rows22325R_109 : rowsJ2 66 67 46 300 ≤ 692833706877017 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_107
#print axioms SieveCert.rows22325R_109
