/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 40–43 of 549

File 10 of 140: the parts `rows22335R_40` … `rows22335R_43` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27010 tests: row 47 columns 35–43, row 47 columns 44–299, row 48 columns
0–34, row 48 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_40 : rowsJ2 47 48 35 44 ≤ 369982092507499 := by decide +kernel

theorem rows22335R_41 : rowsJ2 47 48 44 300 ≤ 279234045022509 := by decide +kernel

theorem rows22335R_42 : rowsJ2 48 49 0 35 ≤ 1743885735188203 := by decide +kernel

theorem rows22335R_43 : rowsJ2 48 49 35 44 ≤ 363246689053874 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_40
#print axioms SieveCert.rows22335R_43
