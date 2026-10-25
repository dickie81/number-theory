/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 761–764 of 1732

File 191 of 430: the parts `rows22310R_761` … `rows22310R_764` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29428 tests: row 119 columns 112–114, row 119 columns 115–399, row 120
columns 0–34, row 120 columns 35–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_761 : rowsJ2 119 120 112 115 ≤ 13145804098973 := by decide +kernel

theorem rows22310R_762 : rowsJ2 119 120 115 400 ≤ 129997308684766 := by decide +kernel

theorem rows22310R_763 : rowsJ2 120 121 0 35 ≤ 95123555413436 := by decide +kernel

theorem rows22310R_764 : rowsJ2 120 121 35 49 ≤ 302257513598494 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_761
#print axioms SieveCert.rows22310R_764
