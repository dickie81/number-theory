/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 950–956 of 4715

File 88 of 351: the parts `rows22250R_950` … `rows22250R_956` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 94436 tests: row 61 columns 54–54, row 61 columns 55–55, row 61 columns
56–56, row 61 columns 57–57, row 61 columns 58–58, row 61 columns 59–59, row 61 columns 60–60), each a sum of
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

theorem rows22250R_950 : rowsJ2 61 62 54 55 ≤ 9321882508006 := by decide +kernel

theorem rows22250R_951 : rowsJ2 61 62 55 56 ≤ 10518403873943 := by decide +kernel

theorem rows22250R_952 : rowsJ2 61 62 56 57 ≤ 11529901494194 := by decide +kernel

theorem rows22250R_953 : rowsJ2 61 62 57 58 ≤ 12378274583225 := by decide +kernel

theorem rows22250R_954 : rowsJ2 61 62 58 59 ≤ 13327917563153 := by decide +kernel

theorem rows22250R_955 : rowsJ2 61 62 59 60 ≤ 14256400547770 := by decide +kernel

theorem rows22250R_956 : rowsJ2 61 62 60 61 ≤ 13669174879608 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_950
#print axioms SieveCert.rows22250R_956
