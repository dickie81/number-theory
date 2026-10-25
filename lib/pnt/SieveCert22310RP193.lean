/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 769–773 of 1732

File 193 of 430: the parts `rows22310R_769` … `rows22310R_773` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29274 tests: row 120 columns 86–87, row 120 columns 88–89, row 120 columns
90–91, row 120 columns 92–93, row 120 columns 94–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_769 : rowsJ2 120 121 86 88 ≤ 270376330088 := by decide +kernel

theorem rows22310R_770 : rowsJ2 120 121 88 90 ≤ 766039121734 := by decide +kernel

theorem rows22310R_771 : rowsJ2 120 121 90 92 ≤ 766100613195 := by decide +kernel

theorem rows22310R_772 : rowsJ2 120 121 92 94 ≤ 579026026763 := by decide +kernel

theorem rows22310R_773 : rowsJ2 120 121 94 96 ≤ 413867316227 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_769
#print axioms SieveCert.rows22310R_773
