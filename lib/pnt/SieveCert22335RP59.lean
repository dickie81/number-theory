/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 228–231 of 549

File 59 of 140: the parts `rows22335R_228` … `rows22335R_231` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 23675 tests: row 87 columns 81–86, row 87 columns 87–299, row 88 columns
0–47, row 88 columns 48–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_228 : rowsJ2 87 88 81 87 ≤ 38662899180869 := by decide +kernel

theorem rows22335R_229 : rowsJ2 87 88 87 300 ≤ 11393150005859 := by decide +kernel

theorem rows22335R_230 : rowsJ2 88 89 0 48 ≤ 764257969102499 := by decide +kernel

theorem rows22335R_231 : rowsJ2 88 89 48 62 ≤ 31092520007720 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_228
#print axioms SieveCert.rows22335R_231
