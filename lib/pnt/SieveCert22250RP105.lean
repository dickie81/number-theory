/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1000–1006 of 5796

File 105 of 465: the parts `rows22250R_1000` … `rows22250R_1006` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 86881 tests: row 62 columns 53–53, row 62 columns 54–54, row 62 columns
55–55, row 62 columns 56–56, row 62 columns 57–57, row 62 columns 58–58, row 62 columns 59–59), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1000 : rowsJ2 62 63 53 54 ≤ 3747644594975 := by decide +kernel

theorem rows22250R_1001 : rowsJ2 62 63 54 55 ≤ 4654609952787 := by decide +kernel

theorem rows22250R_1002 : rowsJ2 62 63 55 56 ≤ 5747610407184 := by decide +kernel

theorem rows22250R_1003 : rowsJ2 62 63 56 57 ≤ 7082380172453 := by decide +kernel

theorem rows22250R_1004 : rowsJ2 62 63 57 58 ≤ 8331339393272 := by decide +kernel

theorem rows22250R_1005 : rowsJ2 62 63 58 59 ≤ 9436643774123 := by decide +kernel

theorem rows22250R_1006 : rowsJ2 62 63 59 60 ≤ 10475850557595 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1000
#print axioms SieveCert.rows22250R_1006
