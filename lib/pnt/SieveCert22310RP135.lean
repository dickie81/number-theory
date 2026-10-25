/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 534–537 of 1732

File 135 of 430: the parts `rows22310R_534` … `rows22310R_537` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24476 tests: row 107 columns 90–91, row 107 columns 92–93, row 107 columns
94–95, row 107 columns 96–97), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_534 : rowsJ2 107 108 90 92 ≤ 1645258013736 := by decide +kernel

theorem rows22310R_535 : rowsJ2 107 108 92 94 ≤ 2724924689416 := by decide +kernel

theorem rows22310R_536 : rowsJ2 107 108 94 96 ≤ 4075378367393 := by decide +kernel

theorem rows22310R_537 : rowsJ2 107 108 96 98 ≤ 4606077250795 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_534
#print axioms SieveCert.rows22310R_537
