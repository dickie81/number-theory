/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2301–2315 of 5796

File 215 of 465: the parts `rows22250R_2301` … `rows22250R_2315` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99397 tests: row 88 columns 84–84, row 88 columns 85–85, row 88 columns
86–86, row 88 columns 87–87, row 88 columns 88–359, row 89 columns 0–16, row 89 columns 17–18, row 89 columns 19–20,
row 89 columns 21–22, row 89 columns 23–24, row 89 columns 25–27, row 89 columns 28–31, row 89 columns 32–35, row 89
columns 36–38, row 89 columns 39–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2301 : rowsJ2 88 89 84 85 ≤ 1071549707375 := by decide +kernel

theorem rows22250R_2302 : rowsJ2 88 89 85 86 ≤ 1334012077481 := by decide +kernel

theorem rows22250R_2303 : rowsJ2 88 89 86 87 ≤ 1659832171569 := by decide +kernel

theorem rows22250R_2304 : rowsJ2 88 89 87 88 ≤ 2184214541602 := by decide +kernel

theorem rows22250R_2305 : rowsJ2 88 89 88 360 ≤ 2827463316031 := by decide +kernel

theorem rows22250R_2306 : rowsJ2 89 90 0 17 ≤ 8792326373 := by decide +kernel

theorem rows22250R_2307 : rowsJ2 89 90 17 19 ≤ 3686586737 := by decide +kernel

theorem rows22250R_2308 : rowsJ2 89 90 19 21 ≤ 728847397 := by decide +kernel

theorem rows22250R_2309 : rowsJ2 89 90 21 23 ≤ 0 := by decide +kernel

theorem rows22250R_2310 : rowsJ2 89 90 23 25 ≤ 0 := by decide +kernel

theorem rows22250R_2311 : rowsJ2 89 90 25 28 ≤ 0 := by decide +kernel

theorem rows22250R_2312 : rowsJ2 89 90 28 32 ≤ 0 := by decide +kernel

theorem rows22250R_2313 : rowsJ2 89 90 32 36 ≤ 545234369436 := by decide +kernel

theorem rows22250R_2314 : rowsJ2 89 90 36 39 ≤ 4776736683085 := by decide +kernel

theorem rows22250R_2315 : rowsJ2 89 90 39 41 ≤ 7547950163120 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2301
#print axioms SieveCert.rows22250R_2315
