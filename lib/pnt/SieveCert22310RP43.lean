/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 173–176 of 1732

File 43 of 430: the parts `rows22310R_173` … `rows22310R_176` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 71 columns 0–34, row 71 columns 35–43, row 71 columns 44–49,
row 71 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22310R_173 : rowsJ2 71 72 0 35 ≤ 936431011979167 := by decide +kernel

theorem rows22310R_174 : rowsJ2 71 72 35 44 ≤ 213844987603516 := by decide +kernel

theorem rows22310R_175 : rowsJ2 71 72 44 50 ≤ 100783843981603 := by decide +kernel

theorem rows22310R_176 : rowsJ2 71 72 50 55 ≤ 104765258367788 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_173
#print axioms SieveCert.rows22310R_176
