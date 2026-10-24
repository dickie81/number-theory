/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 148–150 of 549

File 39 of 140: the parts `rows22335R_148` … `rows22335R_150` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23224 tests: row 75 columns 72–299, row 76 columns 0–34, row 76 columns
35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_148 : rowsJ2 75 76 72 300 ≤ 25036861366122 := by decide +kernel

theorem rows22335R_149 : rowsJ2 76 77 0 35 ≤ 524114224719138 := by decide +kernel

theorem rows22335R_150 : rowsJ2 76 77 35 61 ≤ 802937310237125 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_148
#print axioms SieveCert.rows22335R_150
