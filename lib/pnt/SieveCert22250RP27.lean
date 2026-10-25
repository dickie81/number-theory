/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 325–330 of 5796

File 27 of 465: the parts `rows22250R_325` … `rows22250R_330` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 97289 tests: row 41 columns 31–31, row 41 columns 32–32, row 41 columns
33–33, row 41 columns 34–34, row 41 columns 35–35, row 41 columns 36–36), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_325 : rowsJ2 41 42 31 32 ≤ 390625738970 := by decide +kernel

theorem rows22250R_326 : rowsJ2 41 42 32 33 ≤ 399450498875 := by decide +kernel

theorem rows22250R_327 : rowsJ2 41 42 33 34 ≤ 435523712751 := by decide +kernel

theorem rows22250R_328 : rowsJ2 41 42 34 35 ≤ 450752834942 := by decide +kernel

theorem rows22250R_329 : rowsJ2 41 42 35 36 ≤ 453421995861 := by decide +kernel

theorem rows22250R_330 : rowsJ2 41 42 36 37 ≤ 433484194032 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_325
#print axioms SieveCert.rows22250R_330
