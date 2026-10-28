/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3530–3545 of 5066

File 283 of 387: the parts `rows22240R_3530` … `rows22240R_3545` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93936 in units of a depth-4 test: row 123 columns 60–61, row 123
columns 62–62, row 123 columns 63–63, row 123 columns 64–64, row 123 columns 65–65, row 123 columns 66–66, row 123
columns 67–67, row 123 columns 68–68, row 123 columns 69–69, row 123 columns 70–70, row 123 columns 71–71, row 123
columns 72–72, row 123 columns 73–73, row 123 columns 74–74, row 123 columns 75–76, row 123 columns 77–79), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3530 : rowsJ2 123 124 60 62 ≤ 5527644193502 := by decide +kernel

theorem rows22240R_3531 : rowsJ2 123 124 62 63 ≤ 3455169131850 := by decide +kernel

theorem rows22240R_3532 : rowsJ2 123 124 63 64 ≤ 3829061175302 := by decide +kernel

theorem rows22240R_3533 : rowsJ2 123 124 64 65 ≤ 4153813361798 := by decide +kernel

theorem rows22240R_3534 : rowsJ2 123 124 65 66 ≤ 4406164644123 := by decide +kernel

theorem rows22240R_3535 : rowsJ2 123 124 66 67 ≤ 4607955901921 := by decide +kernel

theorem rows22240R_3536 : rowsJ2 123 124 67 68 ≤ 4735468792287 := by decide +kernel

theorem rows22240R_3537 : rowsJ2 123 124 68 69 ≤ 4810596274924 := by decide +kernel

theorem rows22240R_3538 : rowsJ2 123 124 69 70 ≤ 4809085248097 := by decide +kernel

theorem rows22240R_3539 : rowsJ2 123 124 70 71 ≤ 4752672571834 := by decide +kernel

theorem rows22240R_3540 : rowsJ2 123 124 71 72 ≤ 4616394066846 := by decide +kernel

theorem rows22240R_3541 : rowsJ2 123 124 72 73 ≤ 4164996270220 := by decide +kernel

theorem rows22240R_3542 : rowsJ2 123 124 73 74 ≤ 3466703316835 := by decide +kernel

theorem rows22240R_3543 : rowsJ2 123 124 74 75 ≤ 2831911196307 := by decide +kernel

theorem rows22240R_3544 : rowsJ2 123 124 75 77 ≤ 3935185828403 := by decide +kernel

theorem rows22240R_3545 : rowsJ2 123 124 77 80 ≤ 2309653027257 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3530
#print axioms SieveCert.rows22240R_3545
