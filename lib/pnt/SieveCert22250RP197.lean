/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2385–2395 of 4715

File 197 of 351: the parts `rows22250R_2385` … `rows22250R_2395` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98023 tests: row 94 columns 86–86, row 94 columns 87–87, row 94 columns
88–88, row 94 columns 89–89, row 94 columns 90–90, row 94 columns 91–91, row 94 columns 92–92, row 94 columns 93–93,
row 94 columns 94–339, row 95 columns 0–16, row 95 columns 17–24), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2385 : rowsJ2 94 95 86 87 ≤ 3785546410844 := by decide +kernel

theorem rows22250R_2386 : rowsJ2 94 95 87 88 ≤ 3578092216237 := by decide +kernel

theorem rows22250R_2387 : rowsJ2 94 95 88 89 ≤ 3366854452995 := by decide +kernel

theorem rows22250R_2388 : rowsJ2 94 95 89 90 ≤ 3243505012406 := by decide +kernel

theorem rows22250R_2389 : rowsJ2 94 95 90 91 ≤ 3192394815218 := by decide +kernel

theorem rows22250R_2390 : rowsJ2 94 95 91 92 ≤ 3234201839418 := by decide +kernel

theorem rows22250R_2391 : rowsJ2 94 95 92 93 ≤ 3351993811448 := by decide +kernel

theorem rows22250R_2392 : rowsJ2 94 95 93 94 ≤ 3565648908957 := by decide +kernel

theorem rows22250R_2393 : rowsJ2 94 95 94 340 ≤ 3859742492000 := by decide +kernel

theorem rows22250R_2394 : rowsJ2 95 96 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2395 : rowsJ2 95 96 17 25 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2385
#print axioms SieveCert.rows22250R_2395
