/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 508–512 of 561

File 131 of 143: the parts `rows22322R_508` … `rows22322R_512` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 29408 tests: row 147 columns 0–38, row 147 columns 39–299, row 148 columns
0–38, row 148 columns 39–299, row 149 columns 0–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_508 : rowsJ2 147 148 0 39 ≤ 177470695058131 := by decide +kernel

theorem rows22322R_509 : rowsJ2 147 148 39 300 ≤ 2983798903832325 := by decide +kernel

theorem rows22322R_510 : rowsJ2 148 149 0 39 ≤ 191547005297424 := by decide +kernel

theorem rows22322R_511 : rowsJ2 148 149 39 300 ≤ 2988945161832135 := by decide +kernel

theorem rows22322R_512 : rowsJ2 149 150 0 39 ≤ 203432465746073 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_508
#print axioms SieveCert.rows22322R_512
