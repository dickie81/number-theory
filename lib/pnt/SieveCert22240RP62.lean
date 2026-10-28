/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 608–620 of 5066

File 62 of 387: the parts `rows22240R_608` … `rows22240R_620` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 96491 in units of a depth-4 test: row 51 columns 49–49, row 51 columns
50–50, row 51 columns 51–339, row 52 columns 0–14, row 52 columns 15–18, row 52 columns 19–21, row 52 columns 22–23,
row 52 columns 24–24, row 52 columns 25–25, row 52 columns 26–26, row 52 columns 27–27, row 52 columns 28–28, row 52
columns 29–29), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_608 : rowsJ2 51 52 49 50 ≤ 2741280897970 := by decide +kernel

theorem rows22240R_609 : rowsJ2 51 52 50 51 ≤ 3740457111484 := by decide +kernel

theorem rows22240R_610 : rowsJ2 51 52 51 340 ≤ 4921504620093 := by decide +kernel

theorem rows22240R_611 : rowsJ2 52 53 0 15 ≤ 2397226030840 := by decide +kernel

theorem rows22240R_612 : rowsJ2 52 53 15 19 ≤ 2294483904506 := by decide +kernel

theorem rows22240R_613 : rowsJ2 52 53 19 22 ≤ 1314220929533 := by decide +kernel

theorem rows22240R_614 : rowsJ2 52 53 22 24 ≤ 644811152613 := by decide +kernel

theorem rows22240R_615 : rowsJ2 52 53 24 25 ≤ 263881655197 := by decide +kernel

theorem rows22240R_616 : rowsJ2 52 53 25 26 ≤ 227399358612 := by decide +kernel

theorem rows22240R_617 : rowsJ2 52 53 26 27 ≤ 197562648730 := by decide +kernel

theorem rows22240R_618 : rowsJ2 52 53 27 28 ≤ 170292422885 := by decide +kernel

theorem rows22240R_619 : rowsJ2 52 53 28 29 ≤ 154540324166 := by decide +kernel

theorem rows22240R_620 : rowsJ2 52 53 29 30 ≤ 132534654748 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_608
#print axioms SieveCert.rows22240R_620
