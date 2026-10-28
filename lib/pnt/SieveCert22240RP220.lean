/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2562–2570 of 5066

File 220 of 387: the parts `rows22240R_2562` … `rows22240R_2570` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 93070 in units of a depth-4 test: row 95 columns 84–84, row 95 columns
85–85, row 95 columns 86–86, row 95 columns 87–87, row 95 columns 88–88, row 95 columns 89–89, row 95 columns 90–90,
row 95 columns 91–91, row 95 columns 92–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2562 : rowsJ2 95 96 84 85 ≤ 3821463877349 := by decide +kernel

theorem rows22240R_2563 : rowsJ2 95 96 85 86 ≤ 4686176259380 := by decide +kernel

theorem rows22240R_2564 : rowsJ2 95 96 86 87 ≤ 4686863417794 := by decide +kernel

theorem rows22240R_2565 : rowsJ2 95 96 87 88 ≤ 4019184604647 := by decide +kernel

theorem rows22240R_2566 : rowsJ2 95 96 88 89 ≤ 3514596028342 := by decide +kernel

theorem rows22240R_2567 : rowsJ2 95 96 89 90 ≤ 3460294480949 := by decide +kernel

theorem rows22240R_2568 : rowsJ2 95 96 90 91 ≤ 3496007046970 := by decide +kernel

theorem rows22240R_2569 : rowsJ2 95 96 91 92 ≤ 3606716655655 := by decide +kernel

theorem rows22240R_2570 : rowsJ2 95 96 92 93 ≤ 3811511575191 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2562
#print axioms SieveCert.rows22240R_2570
