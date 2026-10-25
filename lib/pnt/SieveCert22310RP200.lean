/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 798–801 of 1732

File 200 of 430: the parts `rows22310R_798` … `rows22310R_801` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25657 tests: row 121 columns 109–111, row 121 columns 112–115, row 121
columns 116–399, row 122 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_798 : rowsJ2 121 122 109 112 ≤ 9296077432709 := by decide +kernel

theorem rows22310R_799 : rowsJ2 121 122 112 116 ≤ 20669999662446 := by decide +kernel

theorem rows22310R_800 : rowsJ2 121 122 116 400 ≤ 340841313119981 := by decide +kernel

theorem rows22310R_801 : rowsJ2 122 123 0 35 ≤ 102113616375885 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_798
#print axioms SieveCert.rows22310R_801
