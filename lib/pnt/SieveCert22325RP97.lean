/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 372–375 of 561

File 97 of 142: the parts `rows22325R_372` … `rows22325R_375` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24886 tests: row 108 columns 76–299, row 109 columns 0–50, row 109 columns
51–56, row 109 columns 57–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_372 : rowsJ2 108 109 76 300 ≤ 446234738660011 := by decide +kernel

theorem rows22325R_373 : rowsJ2 109 110 0 51 ≤ 322672807977692 := by decide +kernel

theorem rows22325R_374 : rowsJ2 109 110 51 57 ≤ 36757824048540 := by decide +kernel

theorem rows22325R_375 : rowsJ2 109 110 57 63 ≤ 20849915362841 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_372
#print axioms SieveCert.rows22325R_375
