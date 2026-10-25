/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4116–4129 of 5796

File 343 of 465: the parts `rows22250R_4116` … `rows22250R_4129` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98987 tests: row 133 columns 64–64, row 133 columns 65–65, row 133 columns
66–66, row 133 columns 67–67, row 133 columns 68–68, row 133 columns 69–69, row 133 columns 70–70, row 133 columns
71–71, row 133 columns 72–72, row 133 columns 73–73, row 133 columns 74–74, row 133 columns 75–75, row 133 columns
76–76, row 133 columns 77–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4116 : rowsJ2 133 134 64 65 ≤ 3483847114956 := by decide +kernel

theorem rows22250R_4117 : rowsJ2 133 134 65 66 ≤ 3892517182117 := by decide +kernel

theorem rows22250R_4118 : rowsJ2 133 134 66 67 ≤ 4262222657628 := by decide +kernel

theorem rows22250R_4119 : rowsJ2 133 134 67 68 ≤ 4574601519487 := by decide +kernel

theorem rows22250R_4120 : rowsJ2 133 134 68 69 ≤ 4847154135895 := by decide +kernel

theorem rows22250R_4121 : rowsJ2 133 134 69 70 ≤ 5061156593561 := by decide +kernel

theorem rows22250R_4122 : rowsJ2 133 134 70 71 ≤ 5234090437204 := by decide +kernel

theorem rows22250R_4123 : rowsJ2 133 134 71 72 ≤ 5346838749911 := by decide +kernel

theorem rows22250R_4124 : rowsJ2 133 134 72 73 ≤ 5416853401413 := by decide +kernel

theorem rows22250R_4125 : rowsJ2 133 134 73 74 ≤ 5424587494554 := by decide +kernel

theorem rows22250R_4126 : rowsJ2 133 134 74 75 ≤ 5077399737990 := by decide +kernel

theorem rows22250R_4127 : rowsJ2 133 134 75 76 ≤ 4430184930893 := by decide +kernel

theorem rows22250R_4128 : rowsJ2 133 134 76 77 ≤ 3835573129781 := by decide +kernel

theorem rows22250R_4129 : rowsJ2 133 134 77 78 ≤ 3273541188370 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4116
#print axioms SieveCert.rows22250R_4129
