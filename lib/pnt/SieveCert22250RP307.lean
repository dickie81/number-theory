/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3562–3577 of 5796

File 307 of 465: the parts `rows22250R_3562` … `rows22250R_3577` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97926 tests: row 115 columns 65–71, row 115 columns 72–75, row 115 columns
76–78, row 115 columns 79–81, row 115 columns 82–83, row 115 columns 84–85, row 115 columns 86–87, row 115 columns
88–89, row 115 columns 90–91, row 115 columns 92–93, row 115 columns 94–95, row 115 columns 96–97, row 115 columns
98–98, row 115 columns 99–99, row 115 columns 100–100, row 115 columns 101–101), each a sum of refined costs
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

theorem rows22250R_3562 : rowsJ2 115 116 65 72 ≤ 558732734889 := by decide +kernel

theorem rows22250R_3563 : rowsJ2 115 116 72 76 ≤ 0 := by decide +kernel

theorem rows22250R_3564 : rowsJ2 115 116 76 79 ≤ 0 := by decide +kernel

theorem rows22250R_3565 : rowsJ2 115 116 79 82 ≤ 186172846864 := by decide +kernel

theorem rows22250R_3566 : rowsJ2 115 116 82 84 ≤ 632082578709 := by decide +kernel

theorem rows22250R_3567 : rowsJ2 115 116 84 86 ≤ 526443655582 := by decide +kernel

theorem rows22250R_3568 : rowsJ2 115 116 86 88 ≤ 405083413726 := by decide +kernel

theorem rows22250R_3569 : rowsJ2 115 116 88 90 ≤ 800907367398 := by decide +kernel

theorem rows22250R_3570 : rowsJ2 115 116 90 92 ≤ 1695972281253 := by decide +kernel

theorem rows22250R_3571 : rowsJ2 115 116 92 94 ≤ 3109948894220 := by decide +kernel

theorem rows22250R_3572 : rowsJ2 115 116 94 96 ≤ 5065679825128 := by decide +kernel

theorem rows22250R_3573 : rowsJ2 115 116 96 98 ≤ 7550916314507 := by decide +kernel

theorem rows22250R_3574 : rowsJ2 115 116 98 99 ≤ 4881525636949 := by decide +kernel

theorem rows22250R_3575 : rowsJ2 115 116 99 100 ≤ 5699248372993 := by decide +kernel

theorem rows22250R_3576 : rowsJ2 115 116 100 101 ≤ 6610486639943 := by decide +kernel

theorem rows22250R_3577 : rowsJ2 115 116 101 102 ≤ 7576272896413 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3562
#print axioms SieveCert.rows22250R_3577
