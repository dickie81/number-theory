/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 345–348 of 1732

File 86 of 430: the parts `rows22310R_345` … `rows22310R_348` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29933 tests: row 91 columns 44–49, row 91 columns 50–55, row 91 columns
56–62, row 91 columns 63–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_345 : rowsJ2 91 92 44 50 ≤ 126142488842763 := by decide +kernel

theorem rows22310R_346 : rowsJ2 91 92 50 56 ≤ 213156201492782 := by decide +kernel

theorem rows22310R_347 : rowsJ2 91 92 56 63 ≤ 217696825268622 := by decide +kernel

theorem rows22310R_348 : rowsJ2 91 92 63 75 ≤ 271062850551013 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_345
#print axioms SieveCert.rows22310R_348
