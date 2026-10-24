/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 259–262 of 549

File 67 of 140: the parts `rows22335R_259` … `rows22335R_262` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29205 tests: row 92 columns 53–60, row 92 columns 61–65, row 92 columns
66–70, row 92 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_259 : rowsJ2 92 93 53 61 ≤ 0 := by decide +kernel

theorem rows22335R_260 : rowsJ2 92 93 61 66 ≤ 518108788883 := by decide +kernel

theorem rows22335R_261 : rowsJ2 92 93 66 71 ≤ 506254680824 := by decide +kernel

theorem rows22335R_262 : rowsJ2 92 93 71 76 ≤ 367869971560 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_259
#print axioms SieveCert.rows22335R_262
