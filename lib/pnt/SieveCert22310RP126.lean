/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 499–502 of 1732

File 126 of 430: the parts `rows22310R_499` … `rows22310R_502` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29080 tests: row 105 columns 52–67, row 105 columns 68–81, row 105 columns
82–86, row 105 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_499 : rowsJ2 105 106 52 68 ≤ 301282158390606 := by decide +kernel

theorem rows22310R_500 : rowsJ2 105 106 68 82 ≤ 102588626233833 := by decide +kernel

theorem rows22310R_501 : rowsJ2 105 106 82 87 ≤ 9376425577788 := by decide +kernel

theorem rows22310R_502 : rowsJ2 105 106 87 90 ≤ 2062976441065 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_499
#print axioms SieveCert.rows22310R_502
