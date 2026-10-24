/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 510–514 of 561

File 131 of 142: the parts `rows22325R_510` … `rows22325R_514` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 28565 tests: row 148 columns 0–38, row 148 columns 39–299, row 149 columns
0–38, row 149 columns 39–299, row 150 columns 0–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_510 : rowsJ2 148 149 0 39 ≤ 190919730829446 := by decide +kernel

theorem rows22325R_511 : rowsJ2 148 149 39 300 ≤ 2911172417634031 := by decide +kernel

theorem rows22325R_512 : rowsJ2 149 150 0 39 ≤ 202762707805366 := by decide +kernel

theorem rows22325R_513 : rowsJ2 149 150 39 300 ≤ 2918146560655481 := by decide +kernel

theorem rows22325R_514 : rowsJ2 150 151 0 39 ≤ 216061956931525 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_510
#print axioms SieveCert.rows22325R_514
