/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4064–4077 of 5066

File 321 of 387: the parts `rows22240R_4064` … `rows22240R_4077` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96044 in units of a depth-4 test: row 141 columns 64–64, row 141
columns 65–65, row 141 columns 66–66, row 141 columns 67–67, row 141 columns 68–68, row 141 columns 69–69, row 141
columns 70–70, row 141 columns 71–71, row 141 columns 72–72, row 141 columns 73–74, row 141 columns 75–77, row 141
columns 78–82, row 141 columns 83–339, row 142 columns 0–23), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4064 : rowsJ2 141 142 64 65 ≤ 11597931203592 := by decide +kernel

theorem rows22240R_4065 : rowsJ2 141 142 65 66 ≤ 10413120538376 := by decide +kernel

theorem rows22240R_4066 : rowsJ2 141 142 66 67 ≤ 9304404008804 := by decide +kernel

theorem rows22240R_4067 : rowsJ2 141 142 67 68 ≤ 8249231092874 := by decide +kernel

theorem rows22240R_4068 : rowsJ2 141 142 68 69 ≤ 7266227053306 := by decide +kernel

theorem rows22240R_4069 : rowsJ2 141 142 69 70 ≤ 6332809683907 := by decide +kernel

theorem rows22240R_4070 : rowsJ2 141 142 70 71 ≤ 5468076425760 := by decide +kernel

theorem rows22240R_4071 : rowsJ2 141 142 71 72 ≤ 4670678317536 := by decide +kernel

theorem rows22240R_4072 : rowsJ2 141 142 72 73 ≤ 3939372747029 := by decide +kernel

theorem rows22240R_4073 : rowsJ2 141 142 73 75 ≤ 5943619880156 := by decide +kernel

theorem rows22240R_4074 : rowsJ2 141 142 75 78 ≤ 5022844857028 := by decide +kernel

theorem rows22240R_4075 : rowsJ2 141 142 78 83 ≤ 6437663573899 := by decide +kernel

theorem rows22240R_4076 : rowsJ2 141 142 83 340 ≤ 1040564436258336 := by decide +kernel

theorem rows22240R_4077 : rowsJ2 142 143 0 24 ≤ 4612817353505 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4064
#print axioms SieveCert.rows22240R_4077
