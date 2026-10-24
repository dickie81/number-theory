/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 264–267 of 561

File 69 of 142: the parts `rows22325R_264` … `rows22325R_267` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28511 tests: row 92 columns 53–60, row 92 columns 61–65, row 92 columns
66–69, row 92 columns 70–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_264 : rowsJ2 92 93 53 61 ≤ 0 := by decide +kernel

theorem rows22325R_265 : rowsJ2 92 93 61 66 ≤ 693490525874 := by decide +kernel

theorem rows22325R_266 : rowsJ2 92 93 66 70 ≤ 982484916610 := by decide +kernel

theorem rows22325R_267 : rowsJ2 92 93 70 75 ≤ 165008254903 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_264
#print axioms SieveCert.rows22325R_267
