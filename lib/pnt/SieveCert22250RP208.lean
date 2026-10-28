/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2540–2553 of 4715

File 208 of 351: the parts `rows22250R_2540` … `rows22250R_2553` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 98057 in units of a depth-4 test: row 98 columns 61–68, row 98 columns
69–74, row 98 columns 75–77, row 98 columns 78–79, row 98 columns 80–80, row 98 columns 81–81, row 98 columns 82–82,
row 98 columns 83–83, row 98 columns 84–84, row 98 columns 85–85, row 98 columns 86–86, row 98 columns 87–87, row 98
columns 88–88, row 98 columns 89–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2540 : rowsJ2 98 99 61 69 ≤ 0 := by decide +kernel

theorem rows22250R_2541 : rowsJ2 98 99 69 75 ≤ 0 := by decide +kernel

theorem rows22250R_2542 : rowsJ2 98 99 75 78 ≤ 359737033095 := by decide +kernel

theorem rows22250R_2543 : rowsJ2 98 99 78 80 ≤ 1226300467325 := by decide +kernel

theorem rows22250R_2544 : rowsJ2 98 99 80 81 ≤ 1109712711234 := by decide +kernel

theorem rows22250R_2545 : rowsJ2 98 99 81 82 ≤ 1534674196811 := by decide +kernel

theorem rows22250R_2546 : rowsJ2 98 99 82 83 ≤ 2017134450700 := by decide +kernel

theorem rows22250R_2547 : rowsJ2 98 99 83 84 ≤ 2576672335449 := by decide +kernel

theorem rows22250R_2548 : rowsJ2 98 99 84 85 ≤ 2397694863868 := by decide +kernel

theorem rows22250R_2549 : rowsJ2 98 99 85 86 ≤ 2231959711747 := by decide +kernel

theorem rows22250R_2550 : rowsJ2 98 99 86 87 ≤ 2062901058819 := by decide +kernel

theorem rows22250R_2551 : rowsJ2 98 99 87 88 ≤ 1987072319505 := by decide +kernel

theorem rows22250R_2552 : rowsJ2 98 99 88 89 ≤ 1988276090577 := by decide +kernel

theorem rows22250R_2553 : rowsJ2 98 99 89 90 ≤ 2085381300691 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2540
#print axioms SieveCert.rows22250R_2553
