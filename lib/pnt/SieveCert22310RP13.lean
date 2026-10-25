/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 52–55 of 1732

File 13 of 430: the parts `rows22310R_52` … `rows22310R_55` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24804 tests: row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–49,
row 51 columns 50–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_52 : rowsJ2 51 52 0 35 ≤ 1315378998376717 := by decide +kernel

theorem rows22310R_53 : rowsJ2 51 52 35 44 ≤ 624617656801486 := by decide +kernel

theorem rows22310R_54 : rowsJ2 51 52 44 50 ≤ 303132587652912 := by decide +kernel

theorem rows22310R_55 : rowsJ2 51 52 50 400 ≤ 84135563637057 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_52
#print axioms SieveCert.rows22310R_55
