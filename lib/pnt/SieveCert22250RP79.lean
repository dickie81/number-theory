/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 839–850 of 4715

File 79 of 351: the parts `rows22250R_839` … `rows22250R_850` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 93744 in units of a depth-4 test: row 59 columns 24–24, row 59 columns
25–25, row 59 columns 26–26, row 59 columns 27–27, row 59 columns 28–28, row 59 columns 29–29, row 59 columns 30–30,
row 59 columns 31–31, row 59 columns 32–32, row 59 columns 33–33, row 59 columns 34–34, row 59 columns 35–35), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_839 : rowsJ2 59 60 24 25 ≤ 18228530954 := by decide +kernel

theorem rows22250R_840 : rowsJ2 59 60 25 26 ≤ 9128818621 := by decide +kernel

theorem rows22250R_841 : rowsJ2 59 60 26 27 ≤ 4549267162 := by decide +kernel

theorem rows22250R_842 : rowsJ2 59 60 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_843 : rowsJ2 59 60 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_844 : rowsJ2 59 60 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_845 : rowsJ2 59 60 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_846 : rowsJ2 59 60 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_847 : rowsJ2 59 60 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_848 : rowsJ2 59 60 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_849 : rowsJ2 59 60 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_850 : rowsJ2 59 60 35 36 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_839
#print axioms SieveCert.rows22250R_850
