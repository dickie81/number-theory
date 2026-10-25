/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 605–614 of 5796

File 65 of 465: the parts `rows22250R_605` … `rows22250R_614` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 87229 tests: row 52 columns 19–22, row 52 columns 23–24, row 52 columns
25–25, row 52 columns 26–26, row 52 columns 27–27, row 52 columns 28–28, row 52 columns 29–29, row 52 columns 30–30,
row 52 columns 31–31, row 52 columns 32–32), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_605 : rowsJ2 52 53 19 23 ≤ 1311502286977 := by decide +kernel

theorem rows22250R_606 : rowsJ2 52 53 23 25 ≤ 446058689073 := by decide +kernel

theorem rows22250R_607 : rowsJ2 52 53 25 26 ≤ 179466171849 := by decide +kernel

theorem rows22250R_608 : rowsJ2 52 53 26 27 ≤ 155410252336 := by decide +kernel

theorem rows22250R_609 : rowsJ2 52 53 27 28 ≤ 131619017323 := by decide +kernel

theorem rows22250R_610 : rowsJ2 52 53 28 29 ≤ 115726089698 := by decide +kernel

theorem rows22250R_611 : rowsJ2 52 53 29 30 ≤ 104929481975 := by decide +kernel

theorem rows22250R_612 : rowsJ2 52 53 30 31 ≤ 97256342922 := by decide +kernel

theorem rows22250R_613 : rowsJ2 52 53 31 32 ≤ 81364048840 := by decide +kernel

theorem rows22250R_614 : rowsJ2 52 53 32 33 ≤ 68000139078 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_605
#print axioms SieveCert.rows22250R_614
