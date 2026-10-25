/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2355–2369 of 5796

File 219 of 465: the parts `rows22250R_2355` … `rows22250R_2369` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95556 tests: row 90 columns 0–16, row 90 columns 17–19, row 90 columns
20–21, row 90 columns 22–23, row 90 columns 24–26, row 90 columns 27–30, row 90 columns 31–35, row 90 columns 36–38,
row 90 columns 39–40, row 90 columns 41–41, row 90 columns 42–42, row 90 columns 43–43, row 90 columns 44–44, row 90
columns 45–45, row 90 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2355 : rowsJ2 90 91 0 17 ≤ 4782657533 := by decide +kernel

theorem rows22250R_2356 : rowsJ2 90 91 17 20 ≤ 2213749600 := by decide +kernel

theorem rows22250R_2357 : rowsJ2 90 91 20 22 ≤ 0 := by decide +kernel

theorem rows22250R_2358 : rowsJ2 90 91 22 24 ≤ 0 := by decide +kernel

theorem rows22250R_2359 : rowsJ2 90 91 24 27 ≤ 0 := by decide +kernel

theorem rows22250R_2360 : rowsJ2 90 91 27 31 ≤ 0 := by decide +kernel

theorem rows22250R_2361 : rowsJ2 90 91 31 36 ≤ 781491051837 := by decide +kernel

theorem rows22250R_2362 : rowsJ2 90 91 36 39 ≤ 5219404496715 := by decide +kernel

theorem rows22250R_2363 : rowsJ2 90 91 39 41 ≤ 8127772640590 := by decide +kernel

theorem rows22250R_2364 : rowsJ2 90 91 41 42 ≤ 5360754103211 := by decide +kernel

theorem rows22250R_2365 : rowsJ2 90 91 42 43 ≤ 6259775270680 := by decide +kernel

theorem rows22250R_2366 : rowsJ2 90 91 43 44 ≤ 7256520448287 := by decide +kernel

theorem rows22250R_2367 : rowsJ2 90 91 44 45 ≤ 6533594453868 := by decide +kernel

theorem rows22250R_2368 : rowsJ2 90 91 45 46 ≤ 5025569529020 := by decide +kernel

theorem rows22250R_2369 : rowsJ2 90 91 46 47 ≤ 3043724500482 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2355
#print axioms SieveCert.rows22250R_2369
