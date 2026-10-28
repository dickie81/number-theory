/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 751–759 of 5066

File 76 of 387: the parts `rows22240R_751` … `rows22240R_759` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 92454 in units of a depth-4 test: row 56 columns 26–26, row 56 columns
27–27, row 56 columns 28–28, row 56 columns 29–29, row 56 columns 30–30, row 56 columns 31–31, row 56 columns 32–32,
row 56 columns 33–33, row 56 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_751 : rowsJ2 56 57 26 27 ≤ 101057322074 := by decide +kernel

theorem rows22240R_752 : rowsJ2 56 57 27 28 ≤ 83112537669 := by decide +kernel

theorem rows22240R_753 : rowsJ2 56 57 28 29 ≤ 68019356750 := by decide +kernel

theorem rows22240R_754 : rowsJ2 56 57 29 30 ≤ 50920336243 := by decide +kernel

theorem rows22240R_755 : rowsJ2 56 57 30 31 ≤ 38295122423 := by decide +kernel

theorem rows22240R_756 : rowsJ2 56 57 31 32 ≤ 25212361966 := by decide +kernel

theorem rows22240R_757 : rowsJ2 56 57 32 33 ≤ 16613819058 := by decide +kernel

theorem rows22240R_758 : rowsJ2 56 57 33 34 ≤ 8064822139 := by decide +kernel

theorem rows22240R_759 : rowsJ2 56 57 34 35 ≤ 4024650624 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_751
#print axioms SieveCert.rows22240R_759
