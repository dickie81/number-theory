/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 130–132 of 561

File 34 of 142: the parts `rows22325R_130` … `rows22325R_132` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22752 tests: row 72 columns 0–34, row 72 columns 35–53, row 72 columns
54–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_130 : rowsJ2 72 73 0 35 ≤ 548565427347252 := by decide +kernel

theorem rows22325R_131 : rowsJ2 72 73 35 54 ≤ 861314718700227 := by decide +kernel

theorem rows22325R_132 : rowsJ2 72 73 54 68 ≤ 197063238342867 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_130
#print axioms SieveCert.rows22325R_132
