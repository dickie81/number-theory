/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2611–2623 of 5066

File 224 of 387: the parts `rows22240R_2611` … `rows22240R_2623` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 97962 in units of a depth-4 test: row 96 columns 89–89, row 96 columns
90–90, row 96 columns 91–91, row 96 columns 92–92, row 96 columns 93–93, row 96 columns 94–94, row 96 columns 95–95,
row 96 columns 96–339, row 97 columns 0–15, row 97 columns 16–20, row 97 columns 21–28, row 97 columns 29–33, row 97
columns 34–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_2611 : rowsJ2 96 97 89 90 ≤ 3132731441742 := by decide +kernel

theorem rows22240R_2612 : rowsJ2 96 97 90 91 ≤ 3223981756786 := by decide +kernel

theorem rows22240R_2613 : rowsJ2 96 97 91 92 ≤ 3392477887789 := by decide +kernel

theorem rows22240R_2614 : rowsJ2 96 97 92 93 ≤ 3657336253493 := by decide +kernel

theorem rows22240R_2615 : rowsJ2 96 97 93 94 ≤ 4003959249961 := by decide +kernel

theorem rows22240R_2616 : rowsJ2 96 97 94 95 ≤ 4407537439399 := by decide +kernel

theorem rows22240R_2617 : rowsJ2 96 97 95 96 ≤ 4895936217456 := by decide +kernel

theorem rows22240R_2618 : rowsJ2 96 97 96 340 ≤ 5443932828463 := by decide +kernel

theorem rows22240R_2619 : rowsJ2 97 98 0 16 ≤ 0 := by decide +kernel

theorem rows22240R_2620 : rowsJ2 97 98 16 21 ≤ 0 := by decide +kernel

theorem rows22240R_2621 : rowsJ2 97 98 21 29 ≤ 0 := by decide +kernel

theorem rows22240R_2622 : rowsJ2 97 98 29 34 ≤ 5191394603017 := by decide +kernel

theorem rows22240R_2623 : rowsJ2 97 98 34 36 ≤ 8827357394837 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2611
#print axioms SieveCert.rows22240R_2623
