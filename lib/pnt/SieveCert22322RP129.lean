/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 499–502 of 561

File 129 of 143: the parts `rows22322R_499` … `rows22322R_502` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26633 tests: row 142 columns 41–299, row 143 columns 0–40, row 143 columns
41–299, row 144 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_499 : rowsJ2 142 143 41 300 ≤ 2961466456309663 := by decide +kernel

theorem rows22322R_500 : rowsJ2 143 144 0 41 ≤ 169770834217191 := by decide +kernel

theorem rows22322R_501 : rowsJ2 143 144 41 300 ≤ 2956562027829829 := by decide +kernel

theorem rows22322R_502 : rowsJ2 144 145 0 40 ≤ 161159249702136 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_499
#print axioms SieveCert.rows22322R_502
