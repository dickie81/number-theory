/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4834–4846 of 5796

File 399 of 465: the parts `rows22250R_4834` … `rows22250R_4846` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99090 tests: row 156 columns 63–63, row 156 columns 64–64, row 156 columns
65–65, row 156 columns 66–66, row 156 columns 67–67, row 156 columns 68–68, row 156 columns 69–69, row 156 columns
70–70, row 156 columns 71–71, row 156 columns 72–72, row 156 columns 73–74, row 156 columns 75–77, row 156 columns
78–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4834 : rowsJ2 156 157 63 64 ≤ 12200977215215 := by decide +kernel

theorem rows22250R_4835 : rowsJ2 156 157 64 65 ≤ 11010366877640 := by decide +kernel

theorem rows22250R_4836 : rowsJ2 156 157 65 66 ≤ 9888826253115 := by decide +kernel

theorem rows22250R_4837 : rowsJ2 156 157 66 67 ≤ 8834613174250 := by decide +kernel

theorem rows22250R_4838 : rowsJ2 156 157 67 68 ≤ 7846101751946 := by decide +kernel

theorem rows22250R_4839 : rowsJ2 156 157 68 69 ≤ 6921777341903 := by decide +kernel

theorem rows22250R_4840 : rowsJ2 156 157 69 70 ≤ 6060231943217 := by decide +kernel

theorem rows22250R_4841 : rowsJ2 156 157 70 71 ≤ 5260160001625 := by decide +kernel

theorem rows22250R_4842 : rowsJ2 156 157 71 72 ≤ 4520354592676 := by decide +kernel

theorem rows22250R_4843 : rowsJ2 156 157 72 73 ≤ 3839703963247 := by decide +kernel

theorem rows22250R_4844 : rowsJ2 156 157 73 75 ≤ 5869065901137 := by decide +kernel

theorem rows22250R_4845 : rowsJ2 156 157 75 78 ≤ 5123663394065 := by decide +kernel

theorem rows22250R_4846 : rowsJ2 156 157 78 83 ≤ 2364574254748 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4834
#print axioms SieveCert.rows22250R_4846
