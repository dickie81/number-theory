/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 184–187 of 549

File 48 of 140: the parts `rows22335R_184` … `rows22335R_187` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24307 tests: row 81 columns 72–75, row 81 columns 76–80, row 81 columns
81–299, row 82 columns 0–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_184 : rowsJ2 81 82 72 76 ≤ 10391876080364 := by decide +kernel

theorem rows22335R_185 : rowsJ2 81 82 76 81 ≤ 11302075029077 := by decide +kernel

theorem rows22335R_186 : rowsJ2 81 82 81 300 ≤ 3023614062325 := by decide +kernel

theorem rows22335R_187 : rowsJ2 82 83 0 37 ≤ 595962975243772 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_184
#print axioms SieveCert.rows22335R_187
