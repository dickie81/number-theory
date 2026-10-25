/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 149–152 of 1732

File 37 of 430: the parts `rows22310R_149` … `rows22310R_152` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 68 columns 0–34, row 68 columns 35–43, row 68 columns 44–49,
row 68 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22310R_149 : rowsJ2 68 69 0 35 ≤ 1004971287867193 := by decide +kernel

theorem rows22310R_150 : rowsJ2 68 69 35 44 ≤ 263227222093742 := by decide +kernel

theorem rows22310R_151 : rowsJ2 68 69 44 50 ≤ 117550553713260 := by decide +kernel

theorem rows22310R_152 : rowsJ2 68 69 50 55 ≤ 107081204995555 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_149
#print axioms SieveCert.rows22310R_152
