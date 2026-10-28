/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2425–2436 of 4715

File 200 of 351: the parts `rows22250R_2425` … `rows22250R_2436` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 99733 in units of a depth-4 test: row 95 columns 85–85, row 95 columns
86–86, row 95 columns 87–87, row 95 columns 88–88, row 95 columns 89–89, row 95 columns 90–90, row 95 columns 91–91,
row 95 columns 92–92, row 95 columns 93–93, row 95 columns 94–94, row 95 columns 95–339, row 96 columns 0–16), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2425 : rowsJ2 95 96 85 86 ≤ 3511619169359 := by decide +kernel

theorem rows22250R_2426 : rowsJ2 95 96 86 87 ≤ 3303712238371 := by decide +kernel

theorem rows22250R_2427 : rowsJ2 95 96 87 88 ≤ 3109198723046 := by decide +kernel

theorem rows22250R_2428 : rowsJ2 95 96 88 89 ≤ 2948409734993 := by decide +kernel

theorem rows22250R_2429 : rowsJ2 95 96 89 90 ≤ 2877360483605 := by decide +kernel

theorem rows22250R_2430 : rowsJ2 95 96 90 91 ≤ 2881965034887 := by decide +kernel

theorem rows22250R_2431 : rowsJ2 95 96 91 92 ≤ 2980192723425 := by decide +kernel

theorem rows22250R_2432 : rowsJ2 95 96 92 93 ≤ 3156750860015 := by decide +kernel

theorem rows22250R_2433 : rowsJ2 95 96 93 94 ≤ 3431533263424 := by decide +kernel

theorem rows22250R_2434 : rowsJ2 95 96 94 95 ≤ 3790706788839 := by decide +kernel

theorem rows22250R_2435 : rowsJ2 95 96 95 340 ≤ 4207877366155 := by decide +kernel

theorem rows22250R_2436 : rowsJ2 96 97 0 17 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2425
#print axioms SieveCert.rows22250R_2436
