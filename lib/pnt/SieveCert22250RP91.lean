/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 855–862 of 5796

File 91 of 465: the parts `rows22250R_855` … `rows22250R_862` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 90184 tests: row 59 columns 28–28, row 59 columns 29–29, row 59 columns
30–30, row 59 columns 31–31, row 59 columns 32–32, row 59 columns 33–33, row 59 columns 34–34, row 59 columns
35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_855 : rowsJ2 59 60 28 29 ≤ 19167174587 := by decide +kernel

theorem rows22250R_856 : rowsJ2 59 60 29 30 ≤ 12759185310 := by decide +kernel

theorem rows22250R_857 : rowsJ2 59 60 30 31 ≤ 6393121466 := by decide +kernel

theorem rows22250R_858 : rowsJ2 59 60 31 32 ≤ 3188381204 := by decide +kernel

theorem rows22250R_859 : rowsJ2 59 60 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_860 : rowsJ2 59 60 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_861 : rowsJ2 59 60 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_862 : rowsJ2 59 60 35 36 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_855
#print axioms SieveCert.rows22250R_862
