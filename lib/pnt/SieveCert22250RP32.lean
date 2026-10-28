/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 349–354 of 4715

File 32 of 351: the parts `rows22250R_349` … `rows22250R_354` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, work 86678 in units of a depth-4 test: row 43 columns 30–30, row 43 columns
31–31, row 43 columns 32–32, row 43 columns 33–33, row 43 columns 34–34, row 43 columns 35–35), each a sum of
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

theorem rows22250R_349 : rowsJ2 43 44 30 31 ≤ 314958270147 := by decide +kernel

theorem rows22250R_350 : rowsJ2 43 44 31 32 ≤ 302750567570 := by decide +kernel

theorem rows22250R_351 : rowsJ2 43 44 32 33 ≤ 280978294448 := by decide +kernel

theorem rows22250R_352 : rowsJ2 43 44 33 34 ≤ 250774388897 := by decide +kernel

theorem rows22250R_353 : rowsJ2 43 44 34 35 ≤ 217238508790 := by decide +kernel

theorem rows22250R_354 : rowsJ2 43 44 35 36 ≤ 183116107586 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_349
#print axioms SieveCert.rows22250R_354
