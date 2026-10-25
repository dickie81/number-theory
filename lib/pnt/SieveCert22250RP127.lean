/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1432–1440 of 4715

File 127 of 351: the parts `rows22250R_1432` … `rows22250R_1440` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 93784 tests: row 72 columns 48–48, row 72 columns 49–49, row 72 columns
50–50, row 72 columns 51–51, row 72 columns 52–52, row 72 columns 53–53, row 72 columns 54–54, row 72 columns 55–55,
row 72 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1432 : rowsJ2 72 73 48 49 ≤ 2129925578224 := by decide +kernel

theorem rows22250R_1433 : rowsJ2 72 73 49 50 ≤ 2812143331260 := by decide +kernel

theorem rows22250R_1434 : rowsJ2 72 73 50 51 ≤ 3460264920064 := by decide +kernel

theorem rows22250R_1435 : rowsJ2 72 73 51 52 ≤ 4125014396880 := by decide +kernel

theorem rows22250R_1436 : rowsJ2 72 73 52 53 ≤ 4494495409707 := by decide +kernel

theorem rows22250R_1437 : rowsJ2 72 73 53 54 ≤ 4747419535426 := by decide +kernel

theorem rows22250R_1438 : rowsJ2 72 73 54 55 ≤ 4646607370612 := by decide +kernel

theorem rows22250R_1439 : rowsJ2 72 73 55 56 ≤ 4296931541021 := by decide +kernel

theorem rows22250R_1440 : rowsJ2 72 73 56 57 ≤ 3951099909705 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1432
#print axioms SieveCert.rows22250R_1440
