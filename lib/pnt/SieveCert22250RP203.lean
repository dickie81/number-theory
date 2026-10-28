/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2466–2478 of 4715

File 203 of 351: the parts `rows22250R_2466` … `rows22250R_2478` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 96695 in units of a depth-4 test: row 96 columns 85–85, row 96 columns
86–86, row 96 columns 87–87, row 96 columns 88–88, row 96 columns 89–89, row 96 columns 90–90, row 96 columns 91–91,
row 96 columns 92–92, row 96 columns 93–93, row 96 columns 94–94, row 96 columns 95–95, row 96 columns 96–339, row
97 columns 0–16), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2466 : rowsJ2 96 97 85 86 ≤ 3051314432097 := by decide +kernel

theorem rows22250R_2467 : rowsJ2 96 97 86 87 ≤ 2856374571552 := by decide +kernel

theorem rows22250R_2468 : rowsJ2 96 97 87 88 ≤ 2674781155778 := by decide +kernel

theorem rows22250R_2469 : rowsJ2 96 97 88 89 ≤ 2566032606257 := by decide +kernel

theorem rows22250R_2470 : rowsJ2 96 97 89 90 ≤ 2550306012702 := by decide +kernel

theorem rows22250R_2471 : rowsJ2 96 97 90 91 ≤ 2611049070188 := by decide +kernel

theorem rows22250R_2472 : rowsJ2 96 97 91 92 ≤ 2767625409600 := by decide +kernel

theorem rows22250R_2473 : rowsJ2 96 97 92 93 ≤ 3005003866102 := by decide +kernel

theorem rows22250R_2474 : rowsJ2 96 97 93 94 ≤ 3344421155296 := by decide +kernel

theorem rows22250R_2475 : rowsJ2 96 97 94 95 ≤ 3724131126878 := by decide +kernel

theorem rows22250R_2476 : rowsJ2 96 97 95 96 ≤ 4209422396655 := by decide +kernel

theorem rows22250R_2477 : rowsJ2 96 97 96 340 ≤ 4739061454411 := by decide +kernel

theorem rows22250R_2478 : rowsJ2 97 98 0 17 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2466
#print axioms SieveCert.rows22250R_2478
