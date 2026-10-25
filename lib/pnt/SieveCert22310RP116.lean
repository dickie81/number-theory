/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 461–464 of 1732

File 116 of 430: the parts `rows22310R_461` … `rows22310R_464` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27012 tests: row 102 columns 86–89, row 102 columns 90–92, row 102 columns
93–94, row 102 columns 95–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_461 : rowsJ2 102 103 86 90 ≤ 7611888534271 := by decide +kernel

theorem rows22310R_462 : rowsJ2 102 103 90 93 ≤ 3968167447886 := by decide +kernel

theorem rows22310R_463 : rowsJ2 102 103 93 95 ≤ 3477329740833 := by decide +kernel

theorem rows22310R_464 : rowsJ2 102 103 95 97 ≤ 5011303661201 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_461
#print axioms SieveCert.rows22310R_464
