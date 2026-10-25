/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 990–993 of 1732

File 248 of 430: the parts `rows22310R_990` … `rows22310R_993` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29826 tests: row 133 columns 37–68, row 133 columns 69–73, row 133 columns
74–77, row 133 columns 78–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_990 : rowsJ2 133 134 37 69 ≤ 168975025152650 := by decide +kernel

theorem rows22310R_991 : rowsJ2 133 134 69 74 ≤ 2810553182129 := by decide +kernel

theorem rows22310R_992 : rowsJ2 133 134 74 78 ≤ 205570335992 := by decide +kernel

theorem rows22310R_993 : rowsJ2 133 134 78 81 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_990
#print axioms SieveCert.rows22310R_993
