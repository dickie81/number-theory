/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 946–956 of 5066

File 94 of 387: the parts `rows22240R_946` … `rows22240R_956` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 95797 in units of a depth-4 test: row 61 columns 26–26, row 61 columns
27–27, row 61 columns 28–28, row 61 columns 29–29, row 61 columns 30–30, row 61 columns 31–31, row 61 columns 32–32,
row 61 columns 33–33, row 61 columns 34–34, row 61 columns 35–35, row 61 columns 36–36), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_946 : rowsJ2 61 62 26 27 ≤ 24602088803 := by decide +kernel

theorem rows22240R_947 : rowsJ2 61 62 27 28 ≤ 16374398955 := by decide +kernel

theorem rows22240R_948 : rowsJ2 61 62 28 29 ≤ 8205368481 := by decide +kernel

theorem rows22240R_949 : rowsJ2 61 62 29 30 ≤ 4091389332 := by decide +kernel

theorem rows22240R_950 : rowsJ2 61 62 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_951 : rowsJ2 61 62 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_952 : rowsJ2 61 62 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_953 : rowsJ2 61 62 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_954 : rowsJ2 61 62 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_955 : rowsJ2 61 62 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_956 : rowsJ2 61 62 36 37 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_946
#print axioms SieveCert.rows22240R_956
