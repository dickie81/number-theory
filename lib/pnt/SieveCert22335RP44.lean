/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 167–170 of 549

File 44 of 140: the parts `rows22335R_167` … `rows22335R_170` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29512 tests: row 79 columns 0–34, row 79 columns 35–60, row 79 columns 61–67,
row 79 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_167 : rowsJ2 79 80 0 35 ≤ 516636338971307 := by decide +kernel

theorem rows22335R_168 : rowsJ2 79 80 35 61 ≤ 660220184383678 := by decide +kernel

theorem rows22335R_169 : rowsJ2 79 80 61 68 ≤ 9119062071657 := by decide +kernel

theorem rows22335R_170 : rowsJ2 79 80 68 72 ≤ 12590827680735 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_167
#print axioms SieveCert.rows22335R_170
