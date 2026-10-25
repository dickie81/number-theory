/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 417–422 of 5796

File 40 of 465: the parts `rows22250R_417` … `rows22250R_422` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 97857 tests: row 45 columns 31–31, row 45 columns 32–32, row 45 columns
33–33, row 45 columns 34–34, row 45 columns 35–35, row 45 columns 36–36), each a sum of refined costs (`rows2` or
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

theorem rows22250R_417 : rowsJ2 45 46 31 32 ≤ 257256431870 := by decide +kernel

theorem rows22250R_418 : rowsJ2 45 46 32 33 ≤ 264265591686 := by decide +kernel

theorem rows22250R_419 : rowsJ2 45 46 33 34 ≤ 264443747458 := by decide +kernel

theorem rows22250R_420 : rowsJ2 45 46 34 35 ≤ 248601186554 := by decide +kernel

theorem rows22250R_421 : rowsJ2 45 46 35 36 ≤ 230331707083 := by decide +kernel

theorem rows22250R_422 : rowsJ2 45 46 36 37 ≤ 203338319007 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_417
#print axioms SieveCert.rows22250R_422
