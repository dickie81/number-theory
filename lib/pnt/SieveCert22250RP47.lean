/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 466–472 of 5796

File 47 of 465: the parts `rows22250R_466` … `rows22250R_472` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 97559 tests: row 47 columns 29–29, row 47 columns 30–30, row 47 columns
31–31, row 47 columns 32–32, row 47 columns 33–33, row 47 columns 34–34, row 47 columns 35–35), each a sum of
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

theorem rows22250R_466 : rowsJ2 47 48 29 30 ≤ 216905048395 := by decide +kernel

theorem rows22250R_467 : rowsJ2 47 48 30 31 ≤ 204081711604 := by decide +kernel

theorem rows22250R_468 : rowsJ2 47 48 31 32 ≤ 205099269876 := by decide +kernel

theorem rows22250R_469 : rowsJ2 47 48 32 33 ≤ 198562370903 := by decide +kernel

theorem rows22250R_470 : rowsJ2 47 48 33 34 ≤ 185488180105 := by decide +kernel

theorem rows22250R_471 : rowsJ2 47 48 34 35 ≤ 165167850001 := by decide +kernel

theorem rows22250R_472 : rowsJ2 47 48 35 36 ≤ 143767987965 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_466
#print axioms SieveCert.rows22250R_472
