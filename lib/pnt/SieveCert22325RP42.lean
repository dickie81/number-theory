/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 159–162 of 561

File 42 of 142: the parts `rows22325R_159` … `rows22325R_162` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26442 tests: row 77 columns 72–75, row 77 columns 76–299, row 78 columns
0–34, row 78 columns 35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_159 : rowsJ2 77 78 72 76 ≤ 22400770021710 := by decide +kernel

theorem rows22325R_160 : rowsJ2 77 78 76 300 ≤ 9652513770880 := by decide +kernel

theorem rows22325R_161 : rowsJ2 78 79 0 35 ≤ 518733867252686 := by decide +kernel

theorem rows22325R_162 : rowsJ2 78 79 35 61 ≤ 707795211494164 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_159
#print axioms SieveCert.rows22325R_162
