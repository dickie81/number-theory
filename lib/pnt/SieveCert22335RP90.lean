/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 347–350 of 549

File 90 of 140: the parts `rows22335R_347` … `rows22335R_350` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25775 tests: row 105 columns 69–76, row 105 columns 77–299, row 106 columns
0–51, row 106 columns 52–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_347 : rowsJ2 105 106 69 77 ≤ 3551603042729 := by decide +kernel

theorem rows22335R_348 : rowsJ2 105 106 77 300 ≤ 583374966356154 := by decide +kernel

theorem rows22335R_349 : rowsJ2 106 107 0 52 ≤ 370166023497110 := by decide +kernel

theorem rows22335R_350 : rowsJ2 106 107 52 58 ≤ 24363300266726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_347
#print axioms SieveCert.rows22335R_350
