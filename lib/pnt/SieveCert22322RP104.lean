/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 398–401 of 561

File 104 of 143: the parts `rows22322R_398` … `rows22322R_401` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29422 tests: row 114 columns 0–49, row 114 columns 50–55, row 114 columns
56–61, row 114 columns 62–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_398 : rowsJ2 114 115 0 50 ≤ 257025427970861 := by decide +kernel

theorem rows22322R_399 : rowsJ2 114 115 50 56 ≤ 56964765001371 := by decide +kernel

theorem rows22322R_400 : rowsJ2 114 115 56 62 ≤ 33837727523976 := by decide +kernel

theorem rows22322R_401 : rowsJ2 114 115 62 70 ≤ 9806833968455 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_398
#print axioms SieveCert.rows22322R_401
