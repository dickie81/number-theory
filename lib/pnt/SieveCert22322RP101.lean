/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 386–389 of 561

File 101 of 143: the parts `rows22322R_386` … `rows22322R_389` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27548 tests: row 111 columns 63–70, row 111 columns 71–299, row 112 columns
0–49, row 112 columns 50–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_386 : rowsJ2 111 112 63 71 ≤ 3785362506222 := by decide +kernel

theorem rows22322R_387 : rowsJ2 111 112 71 300 ≤ 219110535590008 := by decide +kernel

theorem rows22322R_388 : rowsJ2 112 113 0 50 ≤ 278708180664268 := by decide +kernel

theorem rows22322R_389 : rowsJ2 112 113 50 56 ≤ 48807062651567 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_386
#print axioms SieveCert.rows22322R_389
