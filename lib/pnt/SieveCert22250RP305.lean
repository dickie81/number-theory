/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3531–3546 of 5796

File 305 of 465: the parts `rows22250R_3531` … `rows22250R_3546` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94231 tests: row 114 columns 84–85, row 114 columns 86–87, row 114 columns
88–89, row 114 columns 90–91, row 114 columns 92–93, row 114 columns 94–95, row 114 columns 96–97, row 114 columns
98–98, row 114 columns 99–99, row 114 columns 100–100, row 114 columns 101–101, row 114 columns 102–102, row 114
columns 103–103, row 114 columns 104–104, row 114 columns 105–105, row 114 columns 106–359), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3531 : rowsJ2 114 115 84 86 ≤ 770760526535 := by decide +kernel

theorem rows22250R_3532 : rowsJ2 114 115 86 88 ≤ 606528803238 := by decide +kernel

theorem rows22250R_3533 : rowsJ2 114 115 88 90 ≤ 876610020282 := by decide +kernel

theorem rows22250R_3534 : rowsJ2 114 115 90 92 ≤ 1636031985623 := by decide +kernel

theorem rows22250R_3535 : rowsJ2 114 115 92 94 ≤ 2903423199252 := by decide +kernel

theorem rows22250R_3536 : rowsJ2 114 115 94 96 ≤ 4700451444624 := by decide +kernel

theorem rows22250R_3537 : rowsJ2 114 115 96 98 ≤ 7052112187411 := by decide +kernel

theorem rows22250R_3538 : rowsJ2 114 115 98 99 ≤ 4572577423228 := by decide +kernel

theorem rows22250R_3539 : rowsJ2 114 115 99 100 ≤ 5375233811869 := by decide +kernel

theorem rows22250R_3540 : rowsJ2 114 115 100 101 ≤ 6228797489471 := by decide +kernel

theorem rows22250R_3541 : rowsJ2 114 115 101 102 ≤ 7176106598948 := by decide +kernel

theorem rows22250R_3542 : rowsJ2 114 115 102 103 ≤ 8178251886931 := by decide +kernel

theorem rows22250R_3543 : rowsJ2 114 115 103 104 ≤ 9279349535822 := by decide +kernel

theorem rows22250R_3544 : rowsJ2 114 115 104 105 ≤ 10439802517682 := by decide +kernel

theorem rows22250R_3545 : rowsJ2 114 115 105 106 ≤ 11705095419613 := by decide +kernel

theorem rows22250R_3546 : rowsJ2 114 115 106 360 ≤ 814799204159195 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3531
#print axioms SieveCert.rows22250R_3546
