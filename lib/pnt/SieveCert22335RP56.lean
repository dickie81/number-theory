/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 216–219 of 549

File 56 of 140: the parts `rows22335R_216` … `rows22335R_219` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29224 tests: row 86 columns 40–61, row 86 columns 62–66, row 86 columns
67–70, row 86 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_216 : rowsJ2 86 87 40 62 ≤ 205923145671553 := by decide +kernel

theorem rows22335R_217 : rowsJ2 86 87 62 67 ≤ 1570032945579 := by decide +kernel

theorem rows22335R_218 : rowsJ2 86 87 67 71 ≤ 5262939369720 := by decide +kernel

theorem rows22335R_219 : rowsJ2 86 87 71 76 ≤ 3854159886664 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_216
#print axioms SieveCert.rows22335R_219
