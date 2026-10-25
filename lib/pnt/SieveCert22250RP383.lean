/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4635–4648 of 5796

File 383 of 465: the parts `rows22250R_4635` … `rows22250R_4648` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98175 tests: row 149 columns 69–69, row 149 columns 70–70, row 149 columns
71–71, row 149 columns 72–72, row 149 columns 73–73, row 149 columns 74–74, row 149 columns 75–75, row 149 columns
76–76, row 149 columns 77–78, row 149 columns 79–81, row 149 columns 82–86, row 149 columns 87–359, row 150 columns
0–23, row 150 columns 24–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4635 : rowsJ2 149 150 69 70 ≤ 8338609356294 := by decide +kernel

theorem rows22250R_4636 : rowsJ2 149 150 70 71 ≤ 7454814165871 := by decide +kernel

theorem rows22250R_4637 : rowsJ2 149 150 71 72 ≤ 6612548842539 := by decide +kernel

theorem rows22250R_4638 : rowsJ2 149 150 72 73 ≤ 5827295020481 := by decide +kernel

theorem rows22250R_4639 : rowsJ2 149 150 73 74 ≤ 5080697944559 := by decide +kernel

theorem rows22250R_4640 : rowsJ2 149 150 74 75 ≤ 4388569358690 := by decide +kernel

theorem rows22250R_4641 : rowsJ2 149 150 75 76 ≤ 3749924325282 := by decide +kernel

theorem rows22250R_4642 : rowsJ2 149 150 76 77 ≤ 3163855913625 := by decide +kernel

theorem rows22250R_4643 : rowsJ2 149 150 77 79 ≤ 4775730342257 := by decide +kernel

theorem rows22250R_4644 : rowsJ2 149 150 79 82 ≤ 4038586205388 := by decide +kernel

theorem rows22250R_4645 : rowsJ2 149 150 82 87 ≤ 1654852382307 := by decide +kernel

theorem rows22250R_4646 : rowsJ2 149 150 87 360 ≤ 880561771311101 := by decide +kernel

theorem rows22250R_4647 : rowsJ2 150 151 0 24 ≤ 1681672550294 := by decide +kernel

theorem rows22250R_4648 : rowsJ2 150 151 24 50 ≤ 2953154237859 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4635
#print axioms SieveCert.rows22250R_4648
