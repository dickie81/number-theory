/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 157–160 of 1732

File 39 of 430: the parts `rows22310R_157` … `rows22310R_160` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 69 columns 0–34, row 69 columns 35–43, row 69 columns 44–49,
row 69 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_157 : rowsJ2 69 70 0 35 ≤ 982591344230888 := by decide +kernel

theorem rows22310R_158 : rowsJ2 69 70 35 44 ≤ 246076488430642 := by decide +kernel

theorem rows22310R_159 : rowsJ2 69 70 44 50 ≤ 111412269925821 := by decide +kernel

theorem rows22310R_160 : rowsJ2 69 70 50 55 ≤ 105837441752579 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_157
#print axioms SieveCert.rows22310R_160
