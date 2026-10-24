/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 376–379 of 549

File 98 of 140: the parts `rows22335R_376` … `rows22335R_379` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27038 tests: row 111 columns 57–62, row 111 columns 63–70, row 111 columns
71–299, row 112 columns 0–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_376 : rowsJ2 111 112 57 63 ≤ 22865161275133 := by decide +kernel

theorem rows22335R_377 : rowsJ2 111 112 63 71 ≤ 3315595489242 := by decide +kernel

theorem rows22335R_378 : rowsJ2 111 112 71 300 ≤ 223902168673833 := by decide +kernel

theorem rows22335R_379 : rowsJ2 112 113 0 50 ≤ 277251463285515 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_376
#print axioms SieveCert.rows22335R_379
