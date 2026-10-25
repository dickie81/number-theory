/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 368–371 of 1732

File 92 of 430: the parts `rows22310R_368` … `rows22310R_371` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26412 tests: row 93 columns 92–399, row 94 columns 0–34, row 94 columns
35–43, row 94 columns 44–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_368 : rowsJ2 93 94 92 400 ≤ 10052695636698 := by decide +kernel

theorem rows22310R_369 : rowsJ2 94 95 0 35 ≤ 365755036804169 := by decide +kernel

theorem rows22310R_370 : rowsJ2 94 95 35 44 ≤ 63732022876345 := by decide +kernel

theorem rows22310R_371 : rowsJ2 94 95 44 50 ≤ 148295866684910 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_368
#print axioms SieveCert.rows22310R_371
