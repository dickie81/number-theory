/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 538–541 of 1732

File 136 of 430: the parts `rows22310R_538` … `rows22310R_541` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25024 tests: row 107 columns 98–99, row 107 columns 100–101, row 107 columns
102–103, row 107 columns 104–105), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_538 : rowsJ2 107 108 98 100 ≤ 4144089003853 := by decide +kernel

theorem rows22310R_539 : rowsJ2 107 108 100 102 ≤ 3701874759788 := by decide +kernel

theorem rows22310R_540 : rowsJ2 107 108 102 104 ≤ 3318660488391 := by decide +kernel

theorem rows22310R_541 : rowsJ2 107 108 104 106 ≤ 3205904797009 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_538
#print axioms SieveCert.rows22310R_541
