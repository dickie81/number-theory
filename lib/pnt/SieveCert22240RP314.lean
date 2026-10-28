/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3974–3984 of 5066

File 314 of 387: the parts `rows22240R_3974` … `rows22240R_3984` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 99455 in units of a depth-4 test: row 138 columns 58–58, row 138
columns 59–59, row 138 columns 60–60, row 138 columns 61–61, row 138 columns 62–62, row 138 columns 63–63, row 138
columns 64–64, row 138 columns 65–65, row 138 columns 66–66, row 138 columns 67–67, row 138 columns 68–68), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3974 : rowsJ2 138 139 58 59 ≤ 7238525021104 := by decide +kernel

theorem rows22240R_3975 : rowsJ2 138 139 59 60 ≤ 8120856605999 := by decide +kernel

theorem rows22240R_3976 : rowsJ2 138 139 60 61 ≤ 9041883098385 := by decide +kernel

theorem rows22240R_3977 : rowsJ2 138 139 61 62 ≤ 9979967522453 := by decide +kernel

theorem rows22240R_3978 : rowsJ2 138 139 62 63 ≤ 10873865041348 := by decide +kernel

theorem rows22240R_3979 : rowsJ2 138 139 63 64 ≤ 11703016293576 := by decide +kernel

theorem rows22240R_3980 : rowsJ2 138 139 64 65 ≤ 12487593195130 := by decide +kernel

theorem rows22240R_3981 : rowsJ2 138 139 65 66 ≤ 11304702023100 := by decide +kernel

theorem rows22240R_3982 : rowsJ2 138 139 66 67 ≤ 10198054650623 := by decide +kernel

theorem rows22240R_3983 : rowsJ2 138 139 67 68 ≤ 9144733662980 := by decide +kernel

theorem rows22240R_3984 : rowsJ2 138 139 68 69 ≤ 8163731681693 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3974
#print axioms SieveCert.rows22240R_3984
