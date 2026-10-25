/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 148–150 of 561

File 39 of 143: the parts `rows22322R_148` … `rows22322R_150` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 23371 tests: row 75 columns 72–299, row 76 columns 0–34, row 76 columns
35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_148 : rowsJ2 75 76 72 300 ≤ 26698415269725 := by decide +kernel

theorem rows22322R_149 : rowsJ2 76 77 0 35 ≤ 550529580278494 := by decide +kernel

theorem rows22322R_150 : rowsJ2 76 77 35 61 ≤ 806874706891046 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_148
#print axioms SieveCert.rows22322R_150
