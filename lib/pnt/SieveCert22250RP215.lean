/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2652–2667 of 4715

File 215 of 351: the parts `rows22250R_2652` … `rows22250R_2667` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 95095 in units of a depth-4 test: row 101 columns 34–35, row 101
columns 36–36, row 101 columns 37–37, row 101 columns 38–38, row 101 columns 39–39, row 101 columns 40–40, row 101
columns 41–41, row 101 columns 42–42, row 101 columns 43–43, row 101 columns 44–45, row 101 columns 46–47, row 101
columns 48–49, row 101 columns 50–52, row 101 columns 53–57, row 101 columns 58–66, row 101 columns 67–72), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_2652 : rowsJ2 101 102 34 36 ≤ 15517992271807 := by decide +kernel

theorem rows22250R_2653 : rowsJ2 101 102 36 37 ≤ 10768424201445 := by decide +kernel

theorem rows22250R_2654 : rowsJ2 101 102 37 38 ≤ 12864094669888 := by decide +kernel

theorem rows22250R_2655 : rowsJ2 101 102 38 39 ≤ 14513828924828 := by decide +kernel

theorem rows22250R_2656 : rowsJ2 101 102 39 40 ≤ 16217311401270 := by decide +kernel

theorem rows22250R_2657 : rowsJ2 101 102 40 41 ≤ 14180300923494 := by decide +kernel

theorem rows22250R_2658 : rowsJ2 101 102 41 42 ≤ 12279576618607 := by decide +kernel

theorem rows22250R_2659 : rowsJ2 101 102 42 43 ≤ 10572534147224 := by decide +kernel

theorem rows22250R_2660 : rowsJ2 101 102 43 44 ≤ 9054577924583 := by decide +kernel

theorem rows22250R_2661 : rowsJ2 101 102 44 46 ≤ 13887222907341 := by decide +kernel

theorem rows22250R_2662 : rowsJ2 101 102 46 48 ≤ 8813569967950 := by decide +kernel

theorem rows22250R_2663 : rowsJ2 101 102 48 50 ≤ 4820928895406 := by decide +kernel

theorem rows22250R_2664 : rowsJ2 101 102 50 53 ≤ 2853067403626 := by decide +kernel

theorem rows22250R_2665 : rowsJ2 101 102 53 58 ≤ 375705528028 := by decide +kernel

theorem rows22250R_2666 : rowsJ2 101 102 58 67 ≤ 0 := by decide +kernel

theorem rows22250R_2667 : rowsJ2 101 102 67 73 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2652
#print axioms SieveCert.rows22250R_2667
