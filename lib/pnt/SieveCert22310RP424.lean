/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1700–1706 of 1732

File 424 of 430: the parts `rows22310R_1700` … `rows22310R_1706` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (7 parts, 29636 tests: rows 284–284, rows 285–285, rows 286–286, rows 287–287, rows
288–288, rows 289–289, rows 290–290), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1700 : rows2 284 285 ≤ 7398238734224436 := by decide +kernel

theorem rows22310R_1701 : rows2 285 286 ≤ 7467984710332908 := by decide +kernel

theorem rows22310R_1702 : rows2 286 287 ≤ 7425912298217565 := by decide +kernel

theorem rows22310R_1703 : rows2 287 288 ≤ 7496422545826612 := by decide +kernel

theorem rows22310R_1704 : rows2 288 289 ≤ 7452852824912726 := by decide +kernel

theorem rows22310R_1705 : rows2 289 290 ≤ 7524125644263653 := by decide +kernel

theorem rows22310R_1706 : rows2 290 291 ≤ 7478986266399310 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1700
#print axioms SieveCert.rows22310R_1706
