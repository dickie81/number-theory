/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 225–233 of 4715

File 17 of 351: the parts `rows22250R_225` … `rows22250R_233` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 95830 tests: row 37 columns 26–26, row 37 columns 27–27, row 37 columns
28–28, row 37 columns 29–29, row 37 columns 30–30, row 37 columns 31–31, row 37 columns 32–32, row 37 columns 33–33,
row 37 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_225 : rowsJ2 37 38 26 27 ≤ 718700468888 := by decide +kernel

theorem rows22250R_226 : rowsJ2 37 38 27 28 ≤ 657248467956 := by decide +kernel

theorem rows22250R_227 : rowsJ2 37 38 28 29 ≤ 614344583309 := by decide +kernel

theorem rows22250R_228 : rowsJ2 37 38 29 30 ≤ 587153709324 := by decide +kernel

theorem rows22250R_229 : rowsJ2 37 38 30 31 ≤ 589580496306 := by decide +kernel

theorem rows22250R_230 : rowsJ2 37 38 31 32 ≤ 618889403578 := by decide +kernel

theorem rows22250R_231 : rowsJ2 37 38 32 33 ≤ 681543865615 := by decide +kernel

theorem rows22250R_232 : rowsJ2 37 38 33 34 ≤ 714756690120 := by decide +kernel

theorem rows22250R_233 : rowsJ2 37 38 34 35 ≤ 712215739413 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_225
#print axioms SieveCert.rows22250R_233
