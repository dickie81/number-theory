/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 104–106 of 561

File 27 of 142: the parts `rows22325R_104` … `rows22325R_106` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22935 tests: row 65 columns 0–34, row 65 columns 35–45, row 65 columns
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

theorem rows22325R_104 : rowsJ2 65 66 0 35 ≤ 715528187499722 := by decide +kernel

theorem rows22325R_105 : rowsJ2 65 66 35 46 ≤ 649015857578100 := by decide +kernel

theorem rows22325R_106 : rowsJ2 65 66 46 300 ≤ 716505566282598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_104
#print axioms SieveCert.rows22325R_106
