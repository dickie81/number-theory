/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3532–3546 of 4715

File 272 of 351: the parts `rows22250R_3532` … `rows22250R_3546` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 93448 tests: row 132 columns 73–73, row 132 columns 74–74, row 132 columns
75–76, row 132 columns 77–78, row 132 columns 79–81, row 132 columns 82–85, row 132 columns 86–339, row 133 columns
0–23, row 133 columns 24–32, row 133 columns 33–52, row 133 columns 53–54, row 133 columns 55–56, row 133 columns
57–57, row 133 columns 58–58, row 133 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3532 : rowsJ2 132 133 73 74 ≤ 3921086927228 := by decide +kernel

theorem rows22250R_3533 : rowsJ2 132 133 74 75 ≤ 3339202769803 := by decide +kernel

theorem rows22250R_3534 : rowsJ2 132 133 75 77 ≤ 5153337652071 := by decide +kernel

theorem rows22250R_3535 : rowsJ2 132 133 77 79 ≤ 3429275557270 := by decide +kernel

theorem rows22250R_3536 : rowsJ2 132 133 79 82 ≤ 2710832979673 := by decide +kernel

theorem rows22250R_3537 : rowsJ2 132 133 82 86 ≤ 11379098400688 := by decide +kernel

theorem rows22250R_3538 : rowsJ2 132 133 86 340 ≤ 632245216167958 := by decide +kernel

theorem rows22250R_3539 : rowsJ2 133 134 0 24 ≤ 5510536792274 := by decide +kernel

theorem rows22250R_3540 : rowsJ2 133 134 24 33 ≤ 8571502162968 := by decide +kernel

theorem rows22250R_3541 : rowsJ2 133 134 33 53 ≤ 4857730451609 := by decide +kernel

theorem rows22250R_3542 : rowsJ2 133 134 53 55 ≤ 4794659781401 := by decide +kernel

theorem rows22250R_3543 : rowsJ2 133 134 55 57 ≤ 7087141679111 := by decide +kernel

theorem rows22250R_3544 : rowsJ2 133 134 57 58 ≤ 4518395225364 := by decide +kernel

theorem rows22250R_3545 : rowsJ2 133 134 58 59 ≤ 5225832360401 := by decide +kernel

theorem rows22250R_3546 : rowsJ2 133 134 59 60 ≤ 5974264485028 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3532
#print axioms SieveCert.rows22250R_3546
