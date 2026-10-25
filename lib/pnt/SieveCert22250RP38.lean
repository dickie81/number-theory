/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 396–402 of 4715

File 38 of 351: the parts `rows22250R_396` … `rows22250R_402` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 98221 tests: row 45 columns 30–30, row 45 columns 31–31, row 45 columns
32–32, row 45 columns 33–33, row 45 columns 34–34, row 45 columns 35–35, row 45 columns 36–36), each a sum of
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

theorem rows22250R_396 : rowsJ2 45 46 30 31 ≤ 230683481314 := by decide +kernel

theorem rows22250R_397 : rowsJ2 45 46 31 32 ≤ 212554043439 := by decide +kernel

theorem rows22250R_398 : rowsJ2 45 46 32 33 ≤ 186625617998 := by decide +kernel

theorem rows22250R_399 : rowsJ2 45 46 33 34 ≤ 160485272945 := by decide +kernel

theorem rows22250R_400 : rowsJ2 45 46 34 35 ≤ 133718569105 := by decide +kernel

theorem rows22250R_401 : rowsJ2 45 46 35 36 ≤ 106782670646 := by decide +kernel

theorem rows22250R_402 : rowsJ2 45 46 36 37 ≤ 84216883845 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_396
#print axioms SieveCert.rows22250R_402
