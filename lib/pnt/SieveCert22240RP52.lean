/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 515–526 of 5066

File 52 of 387: the parts `rows22240R_515` … `rows22240R_526` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 97151 in units of a depth-4 test: row 48 columns 45–45, row 48 columns
46–46, row 48 columns 47–47, row 48 columns 48–339, row 49 columns 0–13, row 49 columns 14–17, row 49 columns 18–20,
row 49 columns 21–23, row 49 columns 24–25, row 49 columns 26–26, row 49 columns 27–27, row 49 columns 28–28), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_515 : rowsJ2 48 49 45 46 ≤ 233751682985 := by decide +kernel

theorem rows22240R_516 : rowsJ2 48 49 46 47 ≤ 452169756387 := by decide +kernel

theorem rows22240R_517 : rowsJ2 48 49 47 48 ≤ 961214118259 := by decide +kernel

theorem rows22240R_518 : rowsJ2 48 49 48 340 ≤ 1834582380028 := by decide +kernel

theorem rows22240R_519 : rowsJ2 49 50 0 14 ≤ 1570559779903 := by decide +kernel

theorem rows22240R_520 : rowsJ2 49 50 14 18 ≤ 2700274290116 := by decide +kernel

theorem rows22240R_521 : rowsJ2 49 50 18 21 ≤ 1897692994296 := by decide +kernel

theorem rows22240R_522 : rowsJ2 49 50 21 24 ≤ 1452254296833 := by decide +kernel

theorem rows22240R_523 : rowsJ2 49 50 24 26 ≤ 722818163648 := by decide +kernel

theorem rows22240R_524 : rowsJ2 49 50 26 27 ≤ 298046330020 := by decide +kernel

theorem rows22240R_525 : rowsJ2 49 50 27 28 ≤ 264534247231 := by decide +kernel

theorem rows22240R_526 : rowsJ2 49 50 28 29 ≤ 237130776951 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_515
#print axioms SieveCert.rows22240R_526
