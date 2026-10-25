/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 649–655 of 5796

File 70 of 465: the parts `rows22250R_649` … `rows22250R_655` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 96222 tests: row 53 columns 35–35, row 53 columns 36–36, row 53 columns
37–37, row 53 columns 38–38, row 53 columns 39–39, row 53 columns 40–40, row 53 columns 41–41), each a sum of
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

theorem rows22250R_649 : rowsJ2 53 54 35 36 ≤ 18858869739 := by decide +kernel

theorem rows22250R_650 : rowsJ2 53 54 36 37 ≤ 10819162231 := by decide +kernel

theorem rows22250R_651 : rowsJ2 53 54 37 38 ≤ 6311332889 := by decide +kernel

theorem rows22250R_652 : rowsJ2 53 54 38 39 ≤ 1828067366 := by decide +kernel

theorem rows22250R_653 : rowsJ2 53 54 39 40 ≤ 909822166 := by decide +kernel

theorem rows22250R_654 : rowsJ2 53 54 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_655 : rowsJ2 53 54 41 42 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_649
#print axioms SieveCert.rows22250R_655
