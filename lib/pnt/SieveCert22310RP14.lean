/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 56–59 of 1732

File 14 of 430: the parts `rows22310R_56` … `rows22310R_59` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26235 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns 44–49,
row 52 columns 50–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_56 : rowsJ2 52 53 0 35 ≤ 1299697748281769 := by decide +kernel

theorem rows22310R_57 : rowsJ2 52 53 35 44 ≤ 602143731902777 := by decide +kernel

theorem rows22310R_58 : rowsJ2 52 53 44 50 ≤ 288070574850529 := by decide +kernel

theorem rows22310R_59 : rowsJ2 52 53 50 400 ≤ 118189305493936 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_56
#print axioms SieveCert.rows22310R_59
