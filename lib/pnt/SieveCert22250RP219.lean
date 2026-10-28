/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2720–2736 of 4715

File 219 of 351: the parts `rows22250R_2720` … `rows22250R_2736` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 97618 in units of a depth-4 test: row 102 columns 86–86, row 102
columns 87–87, row 102 columns 88–88, row 102 columns 89–90, row 102 columns 91–92, row 102 columns 93–94, row 102
columns 95–95, row 102 columns 96–96, row 102 columns 97–97, row 102 columns 98–98, row 102 columns 99–99, row 102
columns 100–100, row 102 columns 101–101, row 102 columns 102–339, row 103 columns 0–20, row 103 columns 21–30, row
103 columns 31–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2720 : rowsJ2 102 103 86 87 ≤ 1123346861683 := by decide +kernel

theorem rows22250R_2721 : rowsJ2 102 103 87 88 ≤ 1277986442040 := by decide +kernel

theorem rows22250R_2722 : rowsJ2 102 103 88 89 ≤ 1473968568894 := by decide +kernel

theorem rows22250R_2723 : rowsJ2 102 103 89 91 ≤ 3896712645982 := by decide +kernel

theorem rows22250R_2724 : rowsJ2 102 103 91 93 ≤ 5656949692568 := by decide +kernel

theorem rows22250R_2725 : rowsJ2 102 103 93 95 ≤ 8061385432062 := by decide +kernel

theorem rows22250R_2726 : rowsJ2 102 103 95 96 ≤ 5150880043582 := by decide +kernel

theorem rows22250R_2727 : rowsJ2 102 103 96 97 ≤ 5992280601691 := by decide +kernel

theorem rows22250R_2728 : rowsJ2 102 103 97 98 ≤ 6957632699589 := by decide +kernel

theorem rows22250R_2729 : rowsJ2 102 103 98 99 ≤ 7982687755589 := by decide +kernel

theorem rows22250R_2730 : rowsJ2 102 103 99 100 ≤ 9138040366077 := by decide +kernel

theorem rows22250R_2731 : rowsJ2 102 103 100 101 ≤ 10358345967257 := by decide +kernel

theorem rows22250R_2732 : rowsJ2 102 103 101 102 ≤ 11716125107801 := by decide +kernel

theorem rows22250R_2733 : rowsJ2 102 103 102 340 ≤ 13144908891555 := by decide +kernel

theorem rows22250R_2734 : rowsJ2 103 104 0 21 ≤ 0 := by decide +kernel

theorem rows22250R_2735 : rowsJ2 103 104 21 31 ≤ 3204233953437 := by decide +kernel

theorem rows22250R_2736 : rowsJ2 103 104 31 34 ≤ 13389606795508 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2720
#print axioms SieveCert.rows22250R_2736
