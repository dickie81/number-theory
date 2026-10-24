/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 376–379 of 561

File 98 of 142: the parts `rows22325R_376` … `rows22325R_379` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29967 tests: row 109 columns 63–69, row 109 columns 70–299, row 110 columns
0–50, row 110 columns 51–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_376 : rowsJ2 109 110 63 70 ≤ 1400332371858 := by decide +kernel

theorem rows22325R_377 : rowsJ2 109 110 70 300 ≤ 333854319796449 := by decide +kernel

theorem rows22325R_378 : rowsJ2 110 111 0 51 ≤ 308556093282071 := by decide +kernel

theorem rows22325R_379 : rowsJ2 110 111 51 57 ≤ 41224443416952 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_376
#print axioms SieveCert.rows22325R_379
