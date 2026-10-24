/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 489–492 of 561

File 126 of 142: the parts `rows22325R_489` … `rows22325R_492` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23857 tests: row 138 columns 0–41, row 138 columns 42–51, row 138 columns
52–299, row 139 columns 0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_489 : rowsJ2 138 139 0 42 ≤ 134238691308540 := by decide +kernel

theorem rows22325R_490 : rowsJ2 138 139 42 52 ≤ 124314563331963 := by decide +kernel

theorem rows22325R_491 : rowsJ2 138 139 52 300 ≤ 2782474374603460 := by decide +kernel

theorem rows22325R_492 : rowsJ2 139 140 0 42 ≤ 144436254022058 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_489
#print axioms SieveCert.rows22325R_492
