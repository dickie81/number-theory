/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 478–482 of 561

File 124 of 143: the parts `rows22322R_478` … `rows22322R_482` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 29119 tests: row 134 columns 43–51, row 134 columns 52–299, row 135 columns
0–42, row 135 columns 43–51, row 135 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22322R_478 : rowsJ2 134 135 43 52 ≤ 122482455480360 := by decide +kernel

theorem rows22322R_479 : rowsJ2 134 135 52 300 ≤ 2822552600423570 := by decide +kernel

theorem rows22322R_480 : rowsJ2 135 136 0 43 ≤ 129857323274990 := by decide +kernel

theorem rows22322R_481 : rowsJ2 135 136 43 52 ≤ 118417126009229 := by decide +kernel

theorem rows22322R_482 : rowsJ2 135 136 52 300 ≤ 2881894886023545 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_478
#print axioms SieveCert.rows22322R_482
