/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 60–63 of 1732

File 15 of 430: the parts `rows22310R_60` … `rows22310R_63` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27720 tests: row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–49,
row 53 columns 50–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_60 : rowsJ2 53 54 0 35 ≤ 1283838226507939 := by decide +kernel

theorem rows22310R_61 : rowsJ2 53 54 35 44 ≤ 579534245604676 := by decide +kernel

theorem rows22310R_62 : rowsJ2 53 54 44 50 ≤ 273513087654830 := by decide +kernel

theorem rows22310R_63 : rowsJ2 53 54 50 400 ≤ 148139349094416 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_60
#print axioms SieveCert.rows22310R_63
