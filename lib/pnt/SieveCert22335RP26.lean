/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 101–103 of 549

File 26 of 140: the parts `rows22335R_101` … `rows22335R_103` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22847 tests: row 64 columns 0–34, row 64 columns 35–44, row 64 columns
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

theorem rows22335R_101 : rowsJ2 64 65 0 35 ≤ 753001768087527 := by decide +kernel

theorem rows22335R_102 : rowsJ2 64 65 35 45 ≤ 585243201652150 := by decide +kernel

theorem rows22335R_103 : rowsJ2 64 65 45 300 ≤ 794782840548945 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_101
#print axioms SieveCert.rows22335R_103
