/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 48–50 of 561

File 12 of 142: the parts `rows22325R_48` … `rows22325R_50` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22658 tests: row 50 columns 0–34, row 50 columns 35–43, row 50 columns
44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_48 : rowsJ2 50 51 0 35 ≤ 1595349803025887 := by decide +kernel

theorem rows22325R_49 : rowsJ2 50 51 35 44 ≤ 358635606481078 := by decide +kernel

theorem rows22325R_50 : rowsJ2 50 51 44 300 ≤ 537777583872864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_48
#print axioms SieveCert.rows22325R_50
