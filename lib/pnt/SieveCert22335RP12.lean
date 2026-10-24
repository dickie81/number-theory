/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 48–50 of 549

File 12 of 140: the parts `rows22335R_48` … `rows22335R_50` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22658 tests: row 50 columns 0–34, row 50 columns 35–43, row 50 columns
44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_48 : rowsJ2 50 51 0 35 ≤ 1593288703519803 := by decide +kernel

theorem rows22335R_49 : rowsJ2 50 51 35 44 ≤ 358260507391958 := by decide +kernel

theorem rows22335R_50 : rowsJ2 50 51 44 300 ≤ 537245562720505 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_48
#print axioms SieveCert.rows22335R_50
