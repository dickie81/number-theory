/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 480–483 of 1732

File 121 of 430: the parts `rows22310R_480` … `rows22310R_483` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25047 tests: row 103 columns 101–102, row 103 columns 103–399, row 104
columns 0–34, row 104 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_480 : rowsJ2 103 104 101 103 ≤ 5682761332237 := by decide +kernel

theorem rows22310R_481 : rowsJ2 103 104 103 400 ≤ 2647104947214 := by decide +kernel

theorem rows22310R_482 : rowsJ2 104 105 0 35 ≤ 181900077503437 := by decide +kernel

theorem rows22310R_483 : rowsJ2 104 105 35 44 ≤ 130118383586242 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_480
#print axioms SieveCert.rows22310R_483
