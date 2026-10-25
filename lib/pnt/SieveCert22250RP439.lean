/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5381–5396 of 5796

File 439 of 465: the parts `rows22250R_5381` … `rows22250R_5396` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97507 tests: row 178 columns 55–55, row 178 columns 56–56, row 178 columns
57–57, row 178 columns 58–58, row 178 columns 59–60, row 178 columns 61–359, row 179 columns 0–38, row 179 columns
39–40, row 179 columns 41–42, row 179 columns 43–43, row 179 columns 44–44, row 179 columns 45–45, row 179 columns
46–46, row 179 columns 47–47, row 179 columns 48–48, row 179 columns 49–49), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5381 : rowsJ2 178 179 55 56 ≤ 12873992450925 := by decide +kernel

theorem rows22250R_5382 : rowsJ2 178 179 56 57 ≤ 11424512166829 := by decide +kernel

theorem rows22250R_5383 : rowsJ2 178 179 57 58 ≤ 10071382878593 := by decide +kernel

theorem rows22250R_5384 : rowsJ2 178 179 58 59 ≤ 8812068264720 := by decide +kernel

theorem rows22250R_5385 : rowsJ2 178 179 59 61 ≤ 14209948309890 := by decide +kernel

theorem rows22250R_5386 : rowsJ2 178 179 61 360 ≤ 2577792979362519 := by decide +kernel

theorem rows22250R_5387 : rowsJ2 179 180 0 39 ≤ 10138002332044 := by decide +kernel

theorem rows22250R_5388 : rowsJ2 179 180 39 41 ≤ 11846652819758 := by decide +kernel

theorem rows22250R_5389 : rowsJ2 179 180 41 43 ≤ 16005016945786 := by decide +kernel

theorem rows22250R_5390 : rowsJ2 179 180 43 44 ≤ 9712248110005 := by decide +kernel

theorem rows22250R_5391 : rowsJ2 179 180 44 45 ≤ 10927316733811 := by decide +kernel

theorem rows22250R_5392 : rowsJ2 179 180 45 46 ≤ 12196126146921 := by decide +kernel

theorem rows22250R_5393 : rowsJ2 179 180 46 47 ≤ 13516778229225 := by decide +kernel

theorem rows22250R_5394 : rowsJ2 179 180 47 48 ≤ 14887574312140 := by decide +kernel

theorem rows22250R_5395 : rowsJ2 179 180 48 49 ≤ 16307005647879 := by decide +kernel

theorem rows22250R_5396 : rowsJ2 179 180 49 50 ≤ 17773744977695 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5381
#print axioms SieveCert.rows22250R_5396
