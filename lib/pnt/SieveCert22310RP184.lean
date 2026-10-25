/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 732–736 of 1732

File 184 of 430: the parts `rows22310R_732` … `rows22310R_736` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29717 tests: row 118 columns 89–90, row 118 columns 91–92, row 118 columns
93–94, row 118 columns 95–96, row 118 columns 97–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22310R_732 : rowsJ2 118 119 89 91 ≤ 1121907985422 := by decide +kernel

theorem rows22310R_733 : rowsJ2 118 119 91 93 ≤ 1125824623080 := by decide +kernel

theorem rows22310R_734 : rowsJ2 118 119 93 95 ≤ 897192777309 := by decide +kernel

theorem rows22310R_735 : rowsJ2 118 119 95 97 ≤ 690867082007 := by decide +kernel

theorem rows22310R_736 : rowsJ2 118 119 97 99 ≤ 507580916104 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_732
#print axioms SieveCert.rows22310R_736
