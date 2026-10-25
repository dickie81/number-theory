/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 36–39 of 1732

File 9 of 430: the parts `rows22310R_36` … `rows22310R_39` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26194 tests: row 46 columns 0–34, row 46 columns 35–43, row 46 columns
44–399, row 47 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_36 : rowsJ2 46 47 0 35 ≤ 1392127808093200 := by decide +kernel

theorem rows22310R_37 : rowsJ2 46 47 35 44 ≤ 733455134097242 := by decide +kernel

theorem rows22310R_38 : rowsJ2 46 47 44 400 ≤ 206294750071288 := by decide +kernel

theorem rows22310R_39 : rowsJ2 47 48 0 35 ≤ 1376902785631019 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_36
#print axioms SieveCert.rows22310R_39
