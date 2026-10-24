/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 241–244 of 561

File 63 of 142: the parts `rows22325R_241` … `rows22325R_244` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29862 tests: row 89 columns 51–61, row 89 columns 62–66, row 89 columns
67–70, row 89 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_241 : rowsJ2 89 90 51 62 ≤ 6210237732043 := by decide +kernel

theorem rows22325R_242 : rowsJ2 89 90 62 67 ≤ 1531203661624 := by decide +kernel

theorem rows22325R_243 : rowsJ2 89 90 67 71 ≤ 3072404485728 := by decide +kernel

theorem rows22325R_244 : rowsJ2 89 90 71 76 ≤ 1515012182538 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_241
#print axioms SieveCert.rows22325R_244
