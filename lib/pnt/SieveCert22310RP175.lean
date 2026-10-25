/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 694–698 of 1732

File 175 of 430: the parts `rows22310R_694` … `rows22310R_698` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29900 tests: row 116 columns 91–92, row 116 columns 93–94, row 116 columns
95–96, row 116 columns 97–98, row 116 columns 99–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_694 : rowsJ2 116 117 91 93 ≤ 1701179096626 := by decide +kernel

theorem rows22310R_695 : rowsJ2 116 117 93 95 ≤ 1421410721445 := by decide +kernel

theorem rows22310R_696 : rowsJ2 116 117 95 97 ≤ 1162410742442 := by decide +kernel

theorem rows22310R_697 : rowsJ2 116 117 97 99 ≤ 925382958264 := by decide +kernel

theorem rows22310R_698 : rowsJ2 116 117 99 101 ≤ 711041475017 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_694
#print axioms SieveCert.rows22310R_698
