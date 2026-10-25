/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 233–236 of 1732

File 58 of 430: the parts `rows22310R_233` … `rows22310R_236` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25800 tests: row 77 columns 68–74, row 77 columns 75–399, row 78 columns
0–34, row 78 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_233 : rowsJ2 77 78 68 75 ≤ 226921509251949 := by decide +kernel

theorem rows22310R_234 : rowsJ2 77 78 75 400 ≤ 84075113917375 := by decide +kernel

theorem rows22310R_235 : rowsJ2 78 79 0 35 ≤ 764495599497403 := by decide +kernel

theorem rows22310R_236 : rowsJ2 78 79 35 44 ≤ 122886569494472 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_233
#print axioms SieveCert.rows22310R_236
