/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 922–925 of 1732

File 231 of 430: the parts `rows22310R_922` … `rows22310R_925` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26750 tests: row 128 columns 109–112, row 128 columns 113–399, row 129
columns 0–34, row 129 columns 35–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_922 : rowsJ2 128 129 109 113 ≤ 18906902531282 := by decide +kernel

theorem rows22310R_923 : rowsJ2 128 129 113 400 ≤ 897825241477092 := by decide +kernel

theorem rows22310R_924 : rowsJ2 129 130 0 35 ≤ 146535820015813 := by decide +kernel

theorem rows22310R_925 : rowsJ2 129 130 35 68 ≤ 275081899082107 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_922
#print axioms SieveCert.rows22310R_925
