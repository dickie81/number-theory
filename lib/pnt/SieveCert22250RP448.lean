/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5520–5535 of 5796

File 448 of 465: the parts `rows22250R_5520` … `rows22250R_5535` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98632 tests: row 185 columns 54–54, row 185 columns 55–359, row 186 columns
0–36, row 186 columns 37–38, row 186 columns 39–40, row 186 columns 41–41, row 186 columns 42–42, row 186 columns
43–43, row 186 columns 44–44, row 186 columns 45–45, row 186 columns 46–46, row 186 columns 47–47, row 186 columns
48–48, row 186 columns 49–49, row 186 columns 50–50, row 186 columns 51–51), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5520 : rowsJ2 185 186 54 55 ≤ 10773547730992 := by decide +kernel

theorem rows22250R_5521 : rowsJ2 185 186 55 360 ≤ 2705811160040707 := by decide +kernel

theorem rows22250R_5522 : rowsJ2 186 187 0 37 ≤ 12804391948648 := by decide +kernel

theorem rows22250R_5523 : rowsJ2 186 187 37 39 ≤ 14877197567022 := by decide +kernel

theorem rows22250R_5524 : rowsJ2 186 187 39 41 ≤ 22403396336827 := by decide +kernel

theorem rows22250R_5525 : rowsJ2 186 187 41 42 ≤ 13305303007541 := by decide +kernel

theorem rows22250R_5526 : rowsJ2 186 187 42 43 ≤ 14788186198031 := by decide +kernel

theorem rows22250R_5527 : rowsJ2 186 187 43 44 ≤ 16328858569420 := by decide +kernel

theorem rows22250R_5528 : rowsJ2 186 187 44 45 ≤ 17925552374212 := by decide +kernel

theorem rows22250R_5529 : rowsJ2 186 187 45 46 ≤ 19576727741636 := by decide +kernel

theorem rows22250R_5530 : rowsJ2 186 187 46 47 ≤ 21281063297014 := by decide +kernel

theorem rows22250R_5531 : rowsJ2 186 187 47 48 ≤ 23037448144007 := by decide +kernel

theorem rows22250R_5532 : rowsJ2 186 187 48 49 ≤ 20845862136272 := by decide +kernel

theorem rows22250R_5533 : rowsJ2 186 187 49 50 ≤ 18784137589495 := by decide +kernel

theorem rows22250R_5534 : rowsJ2 186 187 50 51 ≤ 16847850283856 := by decide +kernel

theorem rows22250R_5535 : rowsJ2 186 187 51 52 ≤ 15032901255794 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5520
#print axioms SieveCert.rows22250R_5535
