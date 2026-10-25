/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4782–4797 of 5796

File 395 of 465: the parts `rows22250R_4782` … `rows22250R_4797` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96421 tests: row 154 columns 69–69, row 154 columns 70–70, row 154 columns
71–71, row 154 columns 72–72, row 154 columns 73–73, row 154 columns 74–75, row 154 columns 76–77, row 154 columns
78–81, row 154 columns 82–359, row 155 columns 0–43, row 155 columns 44–49, row 155 columns 50–51, row 155 columns
52–52, row 155 columns 53–53, row 155 columns 54–54, row 155 columns 55–55), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4782 : rowsJ2 154 155 69 70 ≤ 6711756675303 := by decide +kernel

theorem rows22250R_4783 : rowsJ2 154 155 70 71 ≤ 5876643174842 := by decide +kernel

theorem rows22250R_4784 : rowsJ2 154 155 71 72 ≤ 5101035819907 := by decide +kernel

theorem rows22250R_4785 : rowsJ2 154 155 72 73 ≤ 4383783816286 := by decide +kernel

theorem rows22250R_4786 : rowsJ2 154 155 73 74 ≤ 3723826608819 := by decide +kernel

theorem rows22250R_4787 : rowsJ2 154 155 74 76 ≤ 5692179346743 := by decide +kernel

theorem rows22250R_4788 : rowsJ2 154 155 76 78 ≤ 3717150836134 := by decide +kernel

theorem rows22250R_4789 : rowsJ2 154 155 78 82 ≤ 3215182170019 := by decide +kernel

theorem rows22250R_4790 : rowsJ2 154 155 82 360 ≤ 1350404823468414 := by decide +kernel

theorem rows22250R_4791 : rowsJ2 155 156 0 44 ≤ 424063854770 := by decide +kernel

theorem rows22250R_4792 : rowsJ2 155 156 44 50 ≤ 7891677254434 := by decide +kernel

theorem rows22250R_4793 : rowsJ2 155 156 50 52 ≤ 6467012017680 := by decide +kernel

theorem rows22250R_4794 : rowsJ2 155 156 52 53 ≤ 4174314392902 := by decide +kernel

theorem rows22250R_4795 : rowsJ2 155 156 53 54 ≤ 4859987740409 := by decide +kernel

theorem rows22250R_4796 : rowsJ2 155 156 54 55 ≤ 5587244971555 := by decide +kernel

theorem rows22250R_4797 : rowsJ2 155 156 55 56 ≤ 6354433341905 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4782
#print axioms SieveCert.rows22250R_4797
