/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 72–75 of 1732

File 18 of 430: the parts `rows22310R_72` … `rows22310R_75` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23696 tests: row 55 columns 55–399, row 56 columns 0–34, row 56 columns
35–43, row 56 columns 44–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_72 : rowsJ2 55 56 55 400 ≤ 32155123238823 := by decide +kernel

theorem rows22310R_73 : rowsJ2 56 57 0 35 ≤ 1234956576381211 := by decide +kernel

theorem rows22310R_74 : rowsJ2 56 57 35 44 ≤ 511505625823556 := by decide +kernel

theorem rows22310R_75 : rowsJ2 56 57 44 50 ≤ 232883153408289 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_72
#print axioms SieveCert.rows22310R_75
