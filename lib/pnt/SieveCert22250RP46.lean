/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 468–478 of 4715

File 46 of 351: the parts `rows22250R_468` … `rows22250R_478` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 97269 in units of a depth-4 test: row 48 columns 15–19, row 48 columns
20–22, row 48 columns 23–24, row 48 columns 25–25, row 48 columns 26–26, row 48 columns 27–27, row 48 columns 28–28,
row 48 columns 29–29, row 48 columns 30–30, row 48 columns 31–31, row 48 columns 32–32), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_468 : rowsJ2 48 49 15 20 ≤ 2840452589298 := by decide +kernel

theorem rows22250R_469 : rowsJ2 48 49 20 23 ≤ 1144913263399 := by decide +kernel

theorem rows22250R_470 : rowsJ2 48 49 23 25 ≤ 544566921474 := by decide +kernel

theorem rows22250R_471 : rowsJ2 48 49 25 26 ≤ 219597095585 := by decide +kernel

theorem rows22250R_472 : rowsJ2 48 49 26 27 ≤ 189432594686 := by decide +kernel

theorem rows22250R_473 : rowsJ2 48 49 27 28 ≤ 168459042512 := by decide +kernel

theorem rows22250R_474 : rowsJ2 48 49 28 29 ≤ 158131256795 := by decide +kernel

theorem rows22250R_475 : rowsJ2 48 49 29 30 ≤ 141509414056 := by decide +kernel

theorem rows22250R_476 : rowsJ2 48 49 30 31 ≤ 123704140901 := by decide +kernel

theorem rows22250R_477 : rowsJ2 48 49 31 32 ≤ 102394294626 := by decide +kernel

theorem rows22250R_478 : rowsJ2 48 49 32 33 ≤ 81806619634 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_468
#print axioms SieveCert.rows22250R_478
