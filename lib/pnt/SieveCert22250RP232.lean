/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2524–2539 of 5796

File 232 of 465: the parts `rows22250R_2524` … `rows22250R_2539` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94942 tests: row 93 columns 57–57, row 93 columns 58–58, row 93 columns
59–59, row 93 columns 60–60, row 93 columns 61–61, row 93 columns 62–62, row 93 columns 63–64, row 93 columns 65–66,
row 93 columns 67–68, row 93 columns 69–71, row 93 columns 72–75, row 93 columns 76–79, row 93 columns 80–82, row 93
columns 83–83, row 93 columns 84–84, row 93 columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2524 : rowsJ2 93 94 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2525 : rowsJ2 93 94 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2526 : rowsJ2 93 94 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2527 : rowsJ2 93 94 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2528 : rowsJ2 93 94 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2529 : rowsJ2 93 94 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2530 : rowsJ2 93 94 63 65 ≤ 0 := by decide +kernel

theorem rows22250R_2531 : rowsJ2 93 94 65 67 ≤ 0 := by decide +kernel

theorem rows22250R_2532 : rowsJ2 93 94 67 69 ≤ 0 := by decide +kernel

theorem rows22250R_2533 : rowsJ2 93 94 69 72 ≤ 0 := by decide +kernel

theorem rows22250R_2534 : rowsJ2 93 94 72 76 ≤ 0 := by decide +kernel

theorem rows22250R_2535 : rowsJ2 93 94 76 80 ≤ 0 := by decide +kernel

theorem rows22250R_2536 : rowsJ2 93 94 80 83 ≤ 549231381459 := by decide +kernel

theorem rows22250R_2537 : rowsJ2 93 94 83 84 ≤ 559956191154 := by decide +kernel

theorem rows22250R_2538 : rowsJ2 93 94 84 85 ≤ 851110380019 := by decide +kernel

theorem rows22250R_2539 : rowsJ2 93 94 85 86 ≤ 1193793099228 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2524
#print axioms SieveCert.rows22250R_2539
