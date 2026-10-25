/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 554–557 of 1732

File 140 of 430: the parts `rows22310R_554` … `rows22310R_557` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24656 tests: row 108 columns 98–99, row 108 columns 100–101, row 108 columns
102–103, row 108 columns 104–105), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_554 : rowsJ2 108 109 98 100 ≤ 3642631586900 := by decide +kernel

theorem rows22310R_555 : rowsJ2 108 109 100 102 ≤ 3227405552932 := by decide +kernel

theorem rows22310R_556 : rowsJ2 108 109 102 104 ≤ 2928266452298 := by decide +kernel

theorem rows22310R_557 : rowsJ2 108 109 104 106 ≤ 2885352604694 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_554
#print axioms SieveCert.rows22310R_557
