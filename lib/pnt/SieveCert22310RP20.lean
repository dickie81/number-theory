/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 80–83 of 1732

File 20 of 430: the parts `rows22310R_80` … `rows22310R_83` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26810 tests: row 57 columns 44–49, row 57 columns 50–54, row 57 columns
55–399, row 58 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_80 : rowsJ2 57 58 44 50 ≤ 220354763609820 := by decide +kernel

theorem rows22310R_81 : rowsJ2 57 58 50 55 ≤ 152735921957747 := by decide +kernel

theorem rows22310R_82 : rowsJ2 57 58 55 400 ≤ 91802912374849 := by decide +kernel

theorem rows22310R_83 : rowsJ2 58 59 0 35 ≤ 1201006712637122 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_80
#print axioms SieveCert.rows22310R_83
