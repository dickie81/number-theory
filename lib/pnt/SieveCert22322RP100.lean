/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 383–385 of 561

File 100 of 143: the parts `rows22322R_383` … `rows22322R_385` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22692 tests: row 111 columns 0–50, row 111 columns 51–56, row 111 columns
57–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_383 : rowsJ2 111 112 0 51 ≤ 298181027508579 := by decide +kernel

theorem rows22322R_384 : rowsJ2 111 112 51 57 ≤ 45312889569798 := by decide +kernel

theorem rows22322R_385 : rowsJ2 111 112 57 63 ≤ 25137229292470 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_383
#print axioms SieveCert.rows22322R_385
