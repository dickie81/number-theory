/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 130–132 of 549

File 34 of 140: the parts `rows22335R_130` … `rows22335R_132` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22752 tests: row 72 columns 0–34, row 72 columns 35–53, row 72 columns
54–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_130 : rowsJ2 72 73 0 35 ≤ 547905193755481 := by decide +kernel

theorem rows22335R_131 : rowsJ2 72 73 35 54 ≤ 860405140065563 := by decide +kernel

theorem rows22335R_132 : rowsJ2 72 73 54 68 ≤ 196838487428367 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_130
#print axioms SieveCert.rows22335R_132
