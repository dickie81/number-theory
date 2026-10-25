/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 546–549 of 1732

File 138 of 430: the parts `rows22310R_546` … `rows22310R_549` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29036 tests: row 108 columns 54–76, row 108 columns 77–82, row 108 columns
83–86, row 108 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_546 : rowsJ2 108 109 54 77 ≤ 280455357929055 := by decide +kernel

theorem rows22310R_547 : rowsJ2 108 109 77 83 ≤ 15408791555895 := by decide +kernel

theorem rows22310R_548 : rowsJ2 108 109 83 87 ≤ 2152391798074 := by decide +kernel

theorem rows22310R_549 : rowsJ2 108 109 87 90 ≤ 1023161145967 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_546
#print axioms SieveCert.rows22310R_549
