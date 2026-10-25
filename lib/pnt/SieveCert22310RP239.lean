/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 954–957 of 1732

File 239 of 430: the parts `rows22310R_954` … `rows22310R_957` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28493 tests: row 130 columns 103–106, row 130 columns 107–110, row 130
columns 111–399, row 131 columns 0–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_954 : rowsJ2 130 131 103 107 ≤ 6397326973136 := by decide +kernel

theorem rows22310R_955 : rowsJ2 130 131 107 111 ≤ 15105328889350 := by decide +kernel

theorem rows22310R_956 : rowsJ2 130 131 111 400 ≤ 823923823093475 := by decide +kernel

theorem rows22310R_957 : rowsJ2 131 132 0 36 ≤ 177061897595617 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_954
#print axioms SieveCert.rows22310R_957
