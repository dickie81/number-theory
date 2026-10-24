/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 28–30 of 549

File 7 of 140: the parts `rows22335R_28` … `rows22335R_30` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22950 tests: row 43 columns 0–34, row 43 columns 35–299, row 44 columns
0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_28 : rowsJ2 43 44 0 35 ≤ 2136882262568642 := by decide +kernel

theorem rows22335R_29 : rowsJ2 43 44 35 300 ≤ 423357150450740 := by decide +kernel

theorem rows22335R_30 : rowsJ2 44 45 0 35 ≤ 2056945596884204 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_28
#print axioms SieveCert.rows22335R_30
