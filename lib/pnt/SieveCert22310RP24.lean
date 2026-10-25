/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 96–99 of 1732

File 24 of 430: the parts `rows22310R_96` … `rows22310R_99` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24531 tests: row 60 columns 44–49, row 60 columns 50–54, row 60 columns
55–58, row 60 columns 59–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_96 : rowsJ2 60 61 44 50 ≤ 185955802145411 := by decide +kernel

theorem rows22310R_97 : rowsJ2 60 61 50 55 ≤ 134678757305660 := by decide +kernel

theorem rows22310R_98 : rowsJ2 60 61 55 59 ≤ 116799863481512 := by decide +kernel

theorem rows22310R_99 : rowsJ2 60 61 59 400 ≤ 66962462194474 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_96
#print axioms SieveCert.rows22310R_99
