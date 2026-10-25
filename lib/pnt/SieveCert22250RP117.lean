/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1126–1134 of 5796

File 117 of 465: the parts `rows22250R_1126` … `rows22250R_1134` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 98526 tests: row 65 columns 50–50, row 65 columns 51–51, row 65 columns
52–52, row 65 columns 53–53, row 65 columns 54–54, row 65 columns 55–55, row 65 columns 56–56, row 65 columns 57–57,
row 65 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1126 : rowsJ2 65 66 50 51 ≤ 1350332531437 := by decide +kernel

theorem rows22250R_1127 : rowsJ2 65 66 51 52 ≤ 1943799233189 := by decide +kernel

theorem rows22250R_1128 : rowsJ2 65 66 52 53 ≤ 2785869679529 := by decide +kernel

theorem rows22250R_1129 : rowsJ2 65 66 53 54 ≤ 3649708559579 := by decide +kernel

theorem rows22250R_1130 : rowsJ2 65 66 54 55 ≤ 4532972472622 := by decide +kernel

theorem rows22250R_1131 : rowsJ2 65 66 55 56 ≤ 5597409884696 := by decide +kernel

theorem rows22250R_1132 : rowsJ2 65 66 56 57 ≤ 6744853129187 := by decide +kernel

theorem rows22250R_1133 : rowsJ2 65 66 57 58 ≤ 7805317975995 := by decide +kernel

theorem rows22250R_1134 : rowsJ2 65 66 58 59 ≤ 8683409970100 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1126
#print axioms SieveCert.rows22250R_1134
