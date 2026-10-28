/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4011–4024 of 5066

File 317 of 387: the parts `rows22240R_4011` … `rows22240R_4024` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 94212 in units of a depth-4 test: row 139 columns 67–67, row 139
columns 68–68, row 139 columns 69–69, row 139 columns 70–70, row 139 columns 71–71, row 139 columns 72–72, row 139
columns 73–73, row 139 columns 74–75, row 139 columns 76–78, row 139 columns 79–83, row 139 columns 84–339, row 140
columns 0–23, row 140 columns 24–47, row 140 columns 48–51), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_4011 : rowsJ2 139 140 67 68 ≤ 8877418840791 := by decide +kernel

theorem rows22240R_4012 : rowsJ2 139 140 68 69 ≤ 7895795695486 := by decide +kernel

theorem rows22240R_4013 : rowsJ2 139 140 69 70 ≤ 6963605184006 := by decide +kernel

theorem rows22240R_4014 : rowsJ2 139 140 70 71 ≤ 6100188278431 := by decide +kernel

theorem rows22240R_4015 : rowsJ2 139 140 71 72 ≤ 5282643686488 := by decide +kernel

theorem rows22240R_4016 : rowsJ2 139 140 72 73 ≤ 4530775143213 := by decide +kernel

theorem rows22240R_4017 : rowsJ2 139 140 73 74 ≤ 3821572463313 := by decide +kernel

theorem rows22240R_4018 : rowsJ2 139 140 74 76 ≤ 5766237530676 := by decide +kernel

theorem rows22240R_4019 : rowsJ2 139 140 76 79 ≤ 4873261536759 := by decide +kernel

theorem rows22240R_4020 : rowsJ2 139 140 79 84 ≤ 10173234195942 := by decide +kernel

theorem rows22240R_4021 : rowsJ2 139 140 84 340 ≤ 835868683370152 := by decide +kernel

theorem rows22240R_4022 : rowsJ2 140 141 0 24 ≤ 5900922506888 := by decide +kernel

theorem rows22240R_4023 : rowsJ2 140 141 24 48 ≤ 3512426551370 := by decide +kernel

theorem rows22240R_4024 : rowsJ2 140 141 48 52 ≤ 8524360867321 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4011
#print axioms SieveCert.rows22240R_4024
