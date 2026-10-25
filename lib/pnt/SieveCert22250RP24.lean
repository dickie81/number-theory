/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 301–308 of 5796

File 24 of 465: the parts `rows22250R_301` … `rows22250R_308` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 96760 tests: row 40 columns 28–28, row 40 columns 29–29, row 40 columns
30–30, row 40 columns 31–31, row 40 columns 32–32, row 40 columns 33–33, row 40 columns 34–34, row 40 columns
35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_301 : rowsJ2 40 41 28 29 ≤ 511698714315 := by decide +kernel

theorem rows22250R_302 : rowsJ2 40 41 29 30 ≤ 472365855004 := by decide +kernel

theorem rows22250R_303 : rowsJ2 40 41 30 31 ≤ 445557818142 := by decide +kernel

theorem rows22250R_304 : rowsJ2 40 41 31 32 ≤ 429060473930 := by decide +kernel

theorem rows22250R_305 : rowsJ2 40 41 32 33 ≤ 438091391254 := by decide +kernel

theorem rows22250R_306 : rowsJ2 40 41 33 34 ≤ 470285489235 := by decide +kernel

theorem rows22250R_307 : rowsJ2 40 41 34 35 ≤ 511991356606 := by decide +kernel

theorem rows22250R_308 : rowsJ2 40 41 35 36 ≤ 514356129086 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_301
#print axioms SieveCert.rows22250R_308
