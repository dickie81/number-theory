/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 171–174 of 549

File 45 of 140: the parts `rows22335R_171` … `rows22335R_174` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29356 tests: row 79 columns 72–75, row 79 columns 76–299, row 80 columns
0–35, row 80 columns 36–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_171 : rowsJ2 79 80 72 76 ≤ 14906315352975 := by decide +kernel

theorem rows22335R_172 : rowsJ2 79 80 76 300 ≤ 11693368204596 := by decide +kernel

theorem rows22335R_173 : rowsJ2 80 81 0 36 ≤ 561954292127983 := by decide +kernel

theorem rows22335R_174 : rowsJ2 80 81 36 62 ≤ 567458249015432 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_171
#print axioms SieveCert.rows22335R_174
