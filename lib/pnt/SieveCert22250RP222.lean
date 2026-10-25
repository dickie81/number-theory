/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2398–2409 of 5796

File 222 of 465: the parts `rows22250R_2398` … `rows22250R_2409` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99594 tests: row 90 columns 85–85, row 90 columns 86–86, row 90 columns
87–87, row 90 columns 88–88, row 90 columns 89–89, row 90 columns 90–359, row 91 columns 0–16, row 91 columns 17–19,
row 91 columns 20–21, row 91 columns 22–24, row 91 columns 25–28, row 91 columns 29–33), each a sum of refined costs
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

theorem rows22250R_2398 : rowsJ2 90 91 85 86 ≤ 1219411207182 := by decide +kernel

theorem rows22250R_2399 : rowsJ2 90 91 86 87 ≤ 1636086147351 := by decide +kernel

theorem rows22250R_2400 : rowsJ2 90 91 87 88 ≤ 2154050825951 := by decide +kernel

theorem rows22250R_2401 : rowsJ2 90 91 88 89 ≤ 2795229197423 := by decide +kernel

theorem rows22250R_2402 : rowsJ2 90 91 89 90 ≤ 3550326780995 := by decide +kernel

theorem rows22250R_2403 : rowsJ2 90 91 90 360 ≤ 4439730566827 := by decide +kernel

theorem rows22250R_2404 : rowsJ2 91 92 0 17 ≤ 751253086 := by decide +kernel

theorem rows22250R_2405 : rowsJ2 91 92 17 20 ≤ 740006571 := by decide +kernel

theorem rows22250R_2406 : rowsJ2 91 92 20 22 ≤ 0 := by decide +kernel

theorem rows22250R_2407 : rowsJ2 91 92 22 25 ≤ 0 := by decide +kernel

theorem rows22250R_2408 : rowsJ2 91 92 25 29 ≤ 0 := by decide +kernel

theorem rows22250R_2409 : rowsJ2 91 92 29 34 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2398
#print axioms SieveCert.rows22250R_2409
