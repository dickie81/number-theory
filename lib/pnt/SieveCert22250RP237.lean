/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2588–2594 of 5796

File 237 of 465: the parts `rows22250R_2588` … `rows22250R_2594` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 98471 tests: row 94 columns 87–87, row 94 columns 88–88, row 94 columns
89–89, row 94 columns 90–90, row 94 columns 91–91, row 94 columns 92–92, row 94 columns 93–93), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2588 : rowsJ2 94 95 87 88 ≤ 2098558597898 := by decide +kernel

theorem rows22250R_2589 : rowsJ2 94 95 88 89 ≤ 2735945861677 := by decide +kernel

theorem rows22250R_2590 : rowsJ2 94 95 89 90 ≤ 3494139664589 := by decide +kernel

theorem rows22250R_2591 : rowsJ2 94 95 90 91 ≤ 4395739797997 := by decide +kernel

theorem rows22250R_2592 : rowsJ2 94 95 91 92 ≤ 5435452604499 := by decide +kernel

theorem rows22250R_2593 : rowsJ2 94 95 92 93 ≤ 6563107123636 := by decide +kernel

theorem rows22250R_2594 : rowsJ2 94 95 93 94 ≤ 7533970828238 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2588
#print axioms SieveCert.rows22250R_2594
