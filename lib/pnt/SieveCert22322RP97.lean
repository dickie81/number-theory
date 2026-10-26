/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 372–375 of 561

File 97 of 143: the parts `rows22322R_372` … `rows22322R_375` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25473 tests: row 108 columns 76–299, row 109 columns 0–50, row 109 columns
51–56, row 109 columns 57–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_372 : rowsJ2 108 109 76 300 ≤ 342118393159482 := by decide +kernel

theorem rows22322R_373 : rowsJ2 109 110 0 51 ≤ 323989784491425 := by decide +kernel

theorem rows22322R_374 : rowsJ2 109 110 51 57 ≤ 36857899645973 := by decide +kernel

theorem rows22322R_375 : rowsJ2 109 110 57 63 ≤ 20906806062501 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_372
#print axioms SieveCert.rows22322R_375
