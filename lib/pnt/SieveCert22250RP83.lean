/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 772–782 of 5796

File 83 of 465: the parts `rows22250R_772` … `rows22250R_782` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 89067 tests: row 56 columns 56–359, row 57 columns 0–14, row 57 columns
15–19, row 57 columns 20–22, row 57 columns 23–24, row 57 columns 25–25, row 57 columns 26–26, row 57 columns 27–27,
row 57 columns 28–28, row 57 columns 29–29, row 57 columns 30–30), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_772 : rowsJ2 56 57 56 360 ≤ 7484032212149 := by decide +kernel

theorem rows22250R_773 : rowsJ2 57 58 0 15 ≤ 1968219837516 := by decide +kernel

theorem rows22250R_774 : rowsJ2 57 58 15 20 ≤ 1383978202479 := by decide +kernel

theorem rows22250R_775 : rowsJ2 57 58 20 23 ≤ 476107974418 := by decide +kernel

theorem rows22250R_776 : rowsJ2 57 58 23 25 ≤ 210250226634 := by decide +kernel

theorem rows22250R_777 : rowsJ2 57 58 25 26 ≤ 79435891030 := by decide +kernel

theorem rows22250R_778 : rowsJ2 57 58 26 27 ≤ 63523891472 := by decide +kernel

theorem rows22250R_779 : rowsJ2 57 58 27 28 ≤ 50741848383 := by decide +kernel

theorem rows22250R_780 : rowsJ2 57 58 28 29 ≤ 39372874668 := by decide +kernel

theorem rows22250R_781 : rowsJ2 57 58 29 30 ≤ 31118643323 := by decide +kernel

theorem rows22250R_782 : rowsJ2 57 58 30 31 ≤ 21637694862 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_772
#print axioms SieveCert.rows22250R_782
