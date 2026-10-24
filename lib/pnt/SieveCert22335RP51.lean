/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 196–199 of 549

File 51 of 140: the parts `rows22335R_196` … `rows22335R_199` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27876 tests: row 83 columns 62–66, row 83 columns 67–70, row 83 columns
71–74, row 83 columns 75–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_196 : rowsJ2 83 84 62 67 ≤ 1608077066022 := by decide +kernel

theorem rows22335R_197 : rowsJ2 83 84 67 71 ≤ 8225720159209 := by decide +kernel

theorem rows22335R_198 : rowsJ2 83 84 71 75 ≤ 7477847179758 := by decide +kernel

theorem rows22335R_199 : rowsJ2 83 84 75 80 ≤ 8113963304086 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_196
#print axioms SieveCert.rows22335R_199
