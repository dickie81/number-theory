/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1120–1127 of 4715

File 102 of 351: the parts `rows22250R_1120` … `rows22250R_1127` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 99139 tests: row 65 columns 52–52, row 65 columns 53–53, row 65 columns
54–54, row 65 columns 55–55, row 65 columns 56–56, row 65 columns 57–57, row 65 columns 58–58, row 65 columns
59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1120 : rowsJ2 65 66 52 53 ≤ 6394539116836 := by decide +kernel

theorem rows22250R_1121 : rowsJ2 65 66 53 54 ≤ 7231052692955 := by decide +kernel

theorem rows22250R_1122 : rowsJ2 65 66 54 55 ≤ 8092654974896 := by decide +kernel

theorem rows22250R_1123 : rowsJ2 65 66 55 56 ≤ 8930201911654 := by decide +kernel

theorem rows22250R_1124 : rowsJ2 65 66 56 57 ≤ 9581037448532 := by decide +kernel

theorem rows22250R_1125 : rowsJ2 65 66 57 58 ≤ 10062452503215 := by decide +kernel

theorem rows22250R_1126 : rowsJ2 65 66 58 59 ≤ 9599982670085 := by decide +kernel

theorem rows22250R_1127 : rowsJ2 65 66 59 60 ≤ 9143152059663 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1120
#print axioms SieveCert.rows22250R_1127
