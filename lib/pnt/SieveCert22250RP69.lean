/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 641–648 of 5796

File 69 of 465: the parts `rows22250R_641` … `rows22250R_648` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 94170 tests: row 53 columns 27–27, row 53 columns 28–28, row 53 columns
29–29, row 53 columns 30–30, row 53 columns 31–31, row 53 columns 32–32, row 53 columns 33–33, row 53 columns
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

theorem rows22250R_641 : rowsJ2 53 54 27 28 ≤ 112996019646 := by decide +kernel

theorem rows22250R_642 : rowsJ2 53 54 28 29 ≤ 97181595021 := by decide +kernel

theorem rows22250R_643 : rowsJ2 53 54 29 30 ≤ 89315961329 := by decide +kernel

theorem rows22250R_644 : rowsJ2 53 54 30 31 ≤ 76464272295 := by decide +kernel

theorem rows22250R_645 : rowsJ2 53 54 31 32 ≤ 64400124330 := by decide +kernel

theorem rows22250R_646 : rowsJ2 53 54 32 33 ≤ 49312926853 := by decide +kernel

theorem rows22250R_647 : rowsJ2 53 54 33 34 ≤ 38090879019 := by decide +kernel

theorem rows22250R_648 : rowsJ2 53 54 34 35 ≤ 26948580770 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_641
#print axioms SieveCert.rows22250R_648
