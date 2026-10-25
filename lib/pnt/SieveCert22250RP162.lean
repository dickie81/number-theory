/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1621–1627 of 5796

File 162 of 465: the parts `rows22250R_1621` … `rows22250R_1627` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 90725 tests: row 75 columns 53–53, row 75 columns 54–54, row 75 columns
55–55, row 75 columns 56–56, row 75 columns 57–57, row 75 columns 58–58, row 75 columns 59–59), each a sum of
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

theorem rows22250R_1621 : rowsJ2 75 76 53 54 ≤ 3118554736998 := by decide +kernel

theorem rows22250R_1622 : rowsJ2 75 76 54 55 ≤ 3535563191507 := by decide +kernel

theorem rows22250R_1623 : rowsJ2 75 76 55 56 ≤ 3964664463793 := by decide +kernel

theorem rows22250R_1624 : rowsJ2 75 76 56 57 ≤ 4416278525198 := by decide +kernel

theorem rows22250R_1625 : rowsJ2 75 76 57 58 ≤ 4773719402556 := by decide +kernel

theorem rows22250R_1626 : rowsJ2 75 76 58 59 ≤ 4748029210739 := by decide +kernel

theorem rows22250R_1627 : rowsJ2 75 76 59 60 ≤ 4474429894785 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1621
#print axioms SieveCert.rows22250R_1627
