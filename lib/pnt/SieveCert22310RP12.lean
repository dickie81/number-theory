/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 48–51 of 1732

File 12 of 430: the parts `rows22310R_48` … `rows22310R_51` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23426 tests: row 50 columns 0–34, row 50 columns 35–43, row 50 columns 44–49,
row 50 columns 50–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_48 : rowsJ2 50 51 0 35 ≤ 1330892868351965 := by decide +kernel

theorem rows22310R_49 : rowsJ2 50 51 35 44 ≤ 646931186900717 := by decide +kernel

theorem rows22310R_50 : rowsJ2 50 51 44 50 ≤ 318706932413710 := by decide +kernel

theorem rows22310R_51 : rowsJ2 50 51 50 400 ≤ 45013363071452 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_48
#print axioms SieveCert.rows22310R_51
