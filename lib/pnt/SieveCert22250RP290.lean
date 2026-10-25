/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3285–3300 of 5796

File 290 of 465: the parts `rows22250R_3285` … `rows22250R_3300` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96592 tests: row 109 columns 0–18, row 109 columns 19–30, row 109 columns
31–33, row 109 columns 34–35, row 109 columns 36–37, row 109 columns 38–38, row 109 columns 39–39, row 109 columns
40–40, row 109 columns 41–41, row 109 columns 42–42, row 109 columns 43–43, row 109 columns 44–44, row 109 columns
45–45, row 109 columns 46–46, row 109 columns 47–48, row 109 columns 49–50), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3285 : rowsJ2 109 110 0 19 ≤ 0 := by decide +kernel

theorem rows22250R_3286 : rowsJ2 109 110 19 31 ≤ 699156211464 := by decide +kernel

theorem rows22250R_3287 : rowsJ2 109 110 31 34 ≤ 4879865884532 := by decide +kernel

theorem rows22250R_3288 : rowsJ2 109 110 34 36 ≤ 8661469471569 := by decide +kernel

theorem rows22250R_3289 : rowsJ2 109 110 36 38 ≤ 14677012727315 := by decide +kernel

theorem rows22250R_3290 : rowsJ2 109 110 38 39 ≤ 10131367442991 := by decide +kernel

theorem rows22250R_3291 : rowsJ2 109 110 39 40 ≤ 11942213939251 := by decide +kernel

theorem rows22250R_3292 : rowsJ2 109 110 40 41 ≤ 13303716192558 := by decide +kernel

theorem rows22250R_3293 : rowsJ2 109 110 41 42 ≤ 13157197466508 := by decide +kernel

theorem rows22250R_3294 : rowsJ2 109 110 42 43 ≤ 11551940167097 := by decide +kernel

theorem rows22250R_3295 : rowsJ2 109 110 43 44 ≤ 10102455843185 := by decide +kernel

theorem rows22250R_3296 : rowsJ2 109 110 44 45 ≤ 8720973838253 := by decide +kernel

theorem rows22250R_3297 : rowsJ2 109 110 45 46 ≤ 7407380789273 := by decide +kernel

theorem rows22250R_3298 : rowsJ2 109 110 46 47 ≤ 6161680116748 := by decide +kernel

theorem rows22250R_3299 : rowsJ2 109 110 47 49 ≤ 8943171025989 := by decide +kernel

theorem rows22250R_3300 : rowsJ2 109 110 49 51 ≤ 5442916600508 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3285
#print axioms SieveCert.rows22250R_3300
