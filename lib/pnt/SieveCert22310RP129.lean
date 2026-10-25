/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 511–513 of 1732

File 129 of 430: the parts `rows22310R_511` … `rows22310R_513` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22959 tests: row 106 columns 0–34, row 106 columns 35–43, row 106 columns
44–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_511 : rowsJ2 106 107 0 35 ≤ 157039377574237 := by decide +kernel

theorem rows22310R_512 : rowsJ2 106 107 35 44 ≤ 148613932751221 := by decide +kernel

theorem rows22310R_513 : rowsJ2 106 107 44 53 ≤ 255808601285730 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_511
#print axioms SieveCert.rows22310R_513
