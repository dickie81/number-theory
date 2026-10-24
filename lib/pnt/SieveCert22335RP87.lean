/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 335–338 of 549

File 87 of 140: the parts `rows22335R_335` … `rows22335R_338` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25539 tests: row 103 columns 70–77, row 103 columns 78–299, row 104 columns
0–51, row 104 columns 52–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_335 : rowsJ2 103 104 70 78 ≤ 6569479785518 := by decide +kernel

theorem rows22335R_336 : rowsJ2 103 104 78 300 ≤ 710141572724885 := by decide +kernel

theorem rows22335R_337 : rowsJ2 104 105 0 52 ≤ 403075878691562 := by decide +kernel

theorem rows22335R_338 : rowsJ2 104 105 52 58 ≤ 16692357065879 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_335
#print axioms SieveCert.rows22335R_338
