/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 98–100 of 561

File 25 of 142: the parts `rows22325R_98` … `rows22325R_100` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22979 tests: row 63 columns 0–34, row 63 columns 35–44, row 63 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_98 : rowsJ2 63 64 0 35 ≤ 796074408174300 := by decide +kernel

theorem rows22325R_99 : rowsJ2 63 64 35 45 ≤ 580337602357572 := by decide +kernel

theorem rows22325R_100 : rowsJ2 63 64 45 300 ≤ 812377883801134 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_98
#print axioms SieveCert.rows22325R_100
