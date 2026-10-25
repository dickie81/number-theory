/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 812–822 of 5796

File 87 of 465: the parts `rows22250R_812` … `rows22250R_822` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99867 tests: row 58 columns 21–23, row 58 columns 24–24, row 58 columns
25–25, row 58 columns 26–26, row 58 columns 27–27, row 58 columns 28–28, row 58 columns 29–29, row 58 columns 30–30,
row 58 columns 31–31, row 58 columns 32–32, row 58 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_812 : rowsJ2 58 59 21 24 ≤ 346009596871 := by decide +kernel

theorem rows22250R_813 : rowsJ2 58 59 24 25 ≤ 79765400610 := by decide +kernel

theorem rows22250R_814 : rowsJ2 58 59 25 26 ≤ 63775995086 := by decide +kernel

theorem rows22250R_815 : rowsJ2 58 59 26 27 ≤ 50934357931 := by decide +kernel

theorem rows22250R_816 : rowsJ2 58 59 27 28 ≤ 38208931897 := by decide +kernel

theorem rows22250R_817 : rowsJ2 58 59 28 29 ≤ 29481197731 := by decide +kernel

theorem rows22250R_818 : rowsJ2 58 59 29 30 ≤ 20395809358 := by decide +kernel

theorem rows22250R_819 : rowsJ2 58 59 30 31 ≤ 14012924216 := by decide +kernel

theorem rows22250R_820 : rowsJ2 58 59 31 32 ≤ 7237688326 := by decide +kernel

theorem rows22250R_821 : rowsJ2 58 59 32 33 ≤ 4044510211 := by decide +kernel

theorem rows22250R_822 : rowsJ2 58 59 33 34 ≤ 433473978 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_812
#print axioms SieveCert.rows22250R_822
