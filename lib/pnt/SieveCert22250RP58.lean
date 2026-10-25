/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 548–555 of 5796

File 58 of 465: the parts `rows22250R_548` … `rows22250R_555` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 94234 tests: row 50 columns 27–27, row 50 columns 28–28, row 50 columns
29–29, row 50 columns 30–30, row 50 columns 31–31, row 50 columns 32–32, row 50 columns 33–33, row 50 columns
34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_548 : rowsJ2 50 51 27 28 ≤ 178295396904 := by decide +kernel

theorem rows22250R_549 : rowsJ2 50 51 28 29 ≤ 157598091323 := by decide +kernel

theorem rows22250R_550 : rowsJ2 50 51 29 30 ≤ 142157524317 := by decide +kernel

theorem rows22250R_551 : rowsJ2 50 51 30 31 ≤ 138371457354 := by decide +kernel

theorem rows22250R_552 : rowsJ2 50 51 31 32 ≤ 127144760466 := by decide +kernel

theorem rows22250R_553 : rowsJ2 50 51 32 33 ≤ 113707223495 := by decide +kernel

theorem rows22250R_554 : rowsJ2 50 51 33 34 ≤ 94250194611 := by decide +kernel

theorem rows22250R_555 : rowsJ2 50 51 34 35 ≤ 78327623752 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_548
#print axioms SieveCert.rows22250R_555
