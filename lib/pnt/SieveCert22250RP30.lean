/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 347–352 of 5796

File 30 of 465: the parts `rows22250R_347` … `rows22250R_352` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 97785 tests: row 42 columns 31–31, row 42 columns 32–32, row 42 columns
33–33, row 42 columns 34–34, row 42 columns 35–35, row 42 columns 36–36), each a sum of refined costs (`rows2` or
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

theorem rows22250R_347 : rowsJ2 42 43 31 32 ≤ 352508876599 := by decide +kernel

theorem rows22250R_348 : rowsJ2 42 43 32 33 ≤ 365481321308 := by decide +kernel

theorem rows22250R_349 : rowsJ2 42 43 33 34 ≤ 388087343902 := by decide +kernel

theorem rows22250R_350 : rowsJ2 42 43 34 35 ≤ 398975987417 := by decide +kernel

theorem rows22250R_351 : rowsJ2 42 43 35 36 ≤ 384586046720 := by decide +kernel

theorem rows22250R_352 : rowsJ2 42 43 36 37 ≤ 368795644902 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_347
#print axioms SieveCert.rows22250R_352
