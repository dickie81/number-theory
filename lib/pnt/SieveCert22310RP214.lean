/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 855–858 of 1732

File 214 of 430: the parts `rows22310R_855` … `rows22310R_858` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29240 tests: row 124 columns 114–399, row 125 columns 0–34, row 125 columns
35–64, row 125 columns 65–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_855 : rowsJ2 124 125 114 400 ≤ 620909881291114 := by decide +kernel

theorem rows22310R_856 : rowsJ2 125 126 0 35 ≤ 119840971426150 := by decide +kernel

theorem rows22310R_857 : rowsJ2 125 126 35 65 ≤ 358055746717795 := by decide +kernel

theorem rows22310R_858 : rowsJ2 125 126 65 75 ≤ 3583037450013 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_855
#print axioms SieveCert.rows22310R_858
