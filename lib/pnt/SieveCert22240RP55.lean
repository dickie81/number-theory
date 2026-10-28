/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 541–551 of 5066

File 55 of 387: the parts `rows22240R_541` … `rows22240R_551` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 96604 in units of a depth-4 test: row 49 columns 43–43, row 49 columns
44–44, row 49 columns 45–45, row 49 columns 46–46, row 49 columns 47–47, row 49 columns 48–48, row 49 columns
49–339, row 50 columns 0–13, row 50 columns 14–17, row 50 columns 18–21, row 50 columns 22–23), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_541 : rowsJ2 49 50 43 44 ≤ 3177177510 := by decide +kernel

theorem rows22240R_542 : rowsJ2 49 50 44 45 ≤ 80564190570 := by decide +kernel

theorem rows22240R_543 : rowsJ2 49 50 45 46 ≤ 230053584557 := by decide +kernel

theorem rows22240R_544 : rowsJ2 49 50 46 47 ≤ 446183211360 := by decide +kernel

theorem rows22240R_545 : rowsJ2 49 50 47 48 ≤ 950531790097 := by decide +kernel

theorem rows22240R_546 : rowsJ2 49 50 48 49 ≤ 1814765418617 := by decide +kernel

theorem rows22240R_547 : rowsJ2 49 50 49 340 ≤ 2798606447505 := by decide +kernel

theorem rows22240R_548 : rowsJ2 50 51 0 14 ≤ 1657360382966 := by decide +kernel

theorem rows22240R_549 : rowsJ2 50 51 14 18 ≤ 2588758018110 := by decide +kernel

theorem rows22240R_550 : rowsJ2 50 51 18 22 ≤ 2237489026160 := by decide +kernel

theorem rows22240R_551 : rowsJ2 50 51 22 24 ≤ 818237163635 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_541
#print axioms SieveCert.rows22240R_551
