/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 352–355 of 561

File 92 of 142: the parts `rows22325R_352` … `rows22325R_355` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26696 tests: row 105 columns 63–68, row 105 columns 69–76, row 105 columns
77–299, row 106 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_352 : rowsJ2 105 106 63 69 ≤ 0 := by decide +kernel

theorem rows22325R_353 : rowsJ2 105 106 69 77 ≤ 1240943097890 := by decide +kernel

theorem rows22325R_354 : rowsJ2 105 106 77 300 ≤ 578034950299283 := by decide +kernel

theorem rows22325R_355 : rowsJ2 106 107 0 52 ≤ 370595481934297 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_352
#print axioms SieveCert.rows22325R_355
