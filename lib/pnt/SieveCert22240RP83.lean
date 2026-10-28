/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 826–835 of 5066

File 83 of 387: the parts `rows22240R_826` … `rows22240R_835` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 97838 in units of a depth-4 test: row 58 columns 26–26, row 58 columns
27–27, row 58 columns 28–28, row 58 columns 29–29, row 58 columns 30–30, row 58 columns 31–31, row 58 columns 32–32,
row 58 columns 33–33, row 58 columns 34–34, row 58 columns 35–35), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_826 : rowsJ2 58 59 26 27 ≤ 65295243071 := by decide +kernel

theorem rows22240R_827 : rowsJ2 58 59 27 28 ≤ 49665511042 := by decide +kernel

theorem rows22240R_828 : rowsJ2 58 59 28 29 ≤ 37474517470 := by decide +kernel

theorem rows22240R_829 : rowsJ2 58 59 29 30 ≤ 24840228256 := by decide +kernel

theorem rows22240R_830 : rowsJ2 58 59 30 31 ≤ 16721555226 := by decide +kernel

theorem rows22240R_831 : rowsJ2 58 59 31 32 ≤ 8114461079 := by decide +kernel

theorem rows22240R_832 : rowsJ2 58 59 32 33 ≤ 4048129009 := by decide +kernel

theorem rows22240R_833 : rowsJ2 58 59 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_834 : rowsJ2 58 59 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_835 : rowsJ2 58 59 35 36 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_826
#print axioms SieveCert.rows22240R_835
