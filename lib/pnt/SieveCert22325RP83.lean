/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 318–321 of 561

File 83 of 142: the parts `rows22325R_318` … `rows22325R_321` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23411 tests: row 99 columns 88–299, row 100 columns 0–52, row 100 columns
53–59, row 100 columns 60–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_318 : rowsJ2 99 100 88 300 ≤ 457471675420848 := by decide +kernel

theorem rows22325R_319 : rowsJ2 100 101 0 53 ≤ 479824083611982 := by decide +kernel

theorem rows22325R_320 : rowsJ2 100 101 53 60 ≤ 2630101222622 := by decide +kernel

theorem rows22325R_321 : rowsJ2 100 101 60 65 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_318
#print axioms SieveCert.rows22325R_321
