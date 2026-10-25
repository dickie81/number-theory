/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 423–429 of 4715

File 41 of 351: the parts `rows22250R_423` … `rows22250R_429` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 97356 tests: row 46 columns 31–31, row 46 columns 32–32, row 46 columns
33–33, row 46 columns 34–34, row 46 columns 35–35, row 46 columns 36–36, row 46 columns 37–37), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_423 : rowsJ2 46 47 31 32 ≤ 169775300558 := by decide +kernel

theorem rows22250R_424 : rowsJ2 46 47 32 33 ≤ 146458162421 := by decide +kernel

theorem rows22250R_425 : rowsJ2 46 47 33 34 ≤ 121728819674 := by decide +kernel

theorem rows22250R_426 : rowsJ2 46 47 34 35 ≤ 97796764387 := by decide +kernel

theorem rows22250R_427 : rowsJ2 46 47 35 36 ≤ 75173557691 := by decide +kernel

theorem rows22250R_428 : rowsJ2 46 47 36 37 ≤ 56836851027 := by decide +kernel

theorem rows22250R_429 : rowsJ2 46 47 37 38 ≤ 40560877249 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_423
#print axioms SieveCert.rows22250R_429
