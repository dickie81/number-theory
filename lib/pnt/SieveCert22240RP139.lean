/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1472–1482 of 5066

File 139 of 387: the parts `rows22240R_1472` … `rows22240R_1482` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 88840 in units of a depth-4 test: row 72 columns 43–43, row 72 columns
44–44, row 72 columns 45–45, row 72 columns 46–46, row 72 columns 47–47, row 72 columns 48–48, row 72 columns 49–49,
row 72 columns 50–50, row 72 columns 51–51, row 72 columns 52–52, row 72 columns 53–53), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1472 : rowsJ2 72 73 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1473 : rowsJ2 72 73 44 45 ≤ 62886563470 := by decide +kernel

theorem rows22240R_1474 : rowsJ2 72 73 45 46 ≤ 183908114654 := by decide +kernel

theorem rows22240R_1475 : rowsJ2 72 73 46 47 ≤ 358646595651 := by decide +kernel

theorem rows22240R_1476 : rowsJ2 72 73 47 48 ≤ 765740313002 := by decide +kernel

theorem rows22240R_1477 : rowsJ2 72 73 48 49 ≤ 1462946679988 := by decide +kernel

theorem rows22240R_1478 : rowsJ2 72 73 49 50 ≤ 2256055779426 := by decide +kernel

theorem rows22240R_1479 : rowsJ2 72 73 50 51 ≤ 2980019638933 := by decide +kernel

theorem rows22240R_1480 : rowsJ2 72 73 51 52 ≤ 3609572543995 := by decide +kernel

theorem rows22240R_1481 : rowsJ2 72 73 52 53 ≤ 4319080020977 := by decide +kernel

theorem rows22240R_1482 : rowsJ2 72 73 53 54 ≤ 4803838273680 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1472
#print axioms SieveCert.rows22240R_1482
