/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 200–203 of 549

File 52 of 140: the parts `rows22335R_200` … `rows22335R_203` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27421 tests: row 83 columns 80–299, row 84 columns 0–37, row 84 columns
38–61, row 84 columns 62–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_200 : rowsJ2 83 84 80 300 ≤ 13385699270787 := by decide +kernel

theorem rows22335R_201 : rowsJ2 84 85 0 38 ≤ 620189812377686 := by decide +kernel

theorem rows22335R_202 : rowsJ2 84 85 38 62 ≤ 327450346799867 := by decide +kernel

theorem rows22335R_203 : rowsJ2 84 85 62 67 ≤ 1595875217955 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_200
#print axioms SieveCert.rows22335R_203
