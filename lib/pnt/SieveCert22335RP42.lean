/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 159–162 of 549

File 42 of 140: the parts `rows22335R_159` … `rows22335R_162` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26087 tests: row 77 columns 72–75, row 77 columns 76–299, row 78 columns
0–34, row 78 columns 35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_159 : rowsJ2 77 78 72 76 ≤ 20289422439783 := by decide +kernel

theorem rows22335R_160 : rowsJ2 77 78 76 300 ≤ 8339992813224 := by decide +kernel

theorem rows22335R_161 : rowsJ2 78 79 0 35 ≤ 518143809503141 := by decide +kernel

theorem rows22335R_162 : rowsJ2 78 79 35 61 ≤ 707019159059728 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_159
#print axioms SieveCert.rows22335R_162
