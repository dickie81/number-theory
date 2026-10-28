/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 598–607 of 5066

File 61 of 387: the parts `rows22240R_598` … `rows22240R_607` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 99401 in units of a depth-4 test: row 51 columns 39–39, row 51 columns
40–40, row 51 columns 41–41, row 51 columns 42–42, row 51 columns 43–43, row 51 columns 44–44, row 51 columns 45–45,
row 51 columns 46–46, row 51 columns 47–47, row 51 columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_598 : rowsJ2 51 52 39 40 ≤ 3983735748 := by decide +kernel

theorem rows22240R_599 : rowsJ2 51 52 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_600 : rowsJ2 51 52 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_601 : rowsJ2 51 52 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_602 : rowsJ2 51 52 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_603 : rowsJ2 51 52 44 45 ≤ 76412000427 := by decide +kernel

theorem rows22240R_604 : rowsJ2 51 52 45 46 ≤ 223462472106 := by decide +kernel

theorem rows22240R_605 : rowsJ2 51 52 46 47 ≤ 435783135658 := by decide +kernel

theorem rows22240R_606 : rowsJ2 51 52 47 48 ≤ 930433241935 := by decide +kernel

theorem rows22240R_607 : rowsJ2 51 52 48 49 ≤ 1777592480281 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_598
#print axioms SieveCert.rows22240R_607
