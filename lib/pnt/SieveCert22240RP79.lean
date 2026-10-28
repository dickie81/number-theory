/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 781–792 of 5066

File 79 of 387: the parts `rows22240R_781` … `rows22240R_792` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 94207 in units of a depth-4 test: row 56 columns 56–339, row 57 columns
0–14, row 57 columns 15–19, row 57 columns 20–22, row 57 columns 23–23, row 57 columns 24–24, row 57 columns 25–25,
row 57 columns 26–26, row 57 columns 27–27, row 57 columns 28–28, row 57 columns 29–29, row 57 columns 30–30), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_781 : rowsJ2 56 57 56 340 ≤ 12313965615244 := by decide +kernel

theorem rows22240R_782 : rowsJ2 57 58 0 15 ≤ 2494372638094 := by decide +kernel

theorem rows22240R_783 : rowsJ2 57 58 15 20 ≤ 1754336890973 := by decide +kernel

theorem rows22240R_784 : rowsJ2 57 58 20 23 ≤ 604473490347 := by decide +kernel

theorem rows22240R_785 : rowsJ2 57 58 23 24 ≤ 145751631226 := by decide +kernel

theorem rows22240R_786 : rowsJ2 57 58 24 25 ≤ 121341972039 := by decide +kernel

theorem rows22240R_787 : rowsJ2 57 58 25 26 ≤ 100930719045 := by decide +kernel

theorem rows22240R_788 : rowsJ2 57 58 26 27 ≤ 81271564919 := by decide +kernel

theorem rows22240R_789 : rowsJ2 57 58 27 28 ≤ 66646264369 := by decide +kernel

theorem rows22240R_790 : rowsJ2 57 58 28 29 ≤ 50555663857 := by decide +kernel

theorem rows22240R_791 : rowsJ2 57 58 29 30 ≤ 37877617686 := by decide +kernel

theorem rows22240R_792 : rowsJ2 57 58 30 31 ≤ 25294898561 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_781
#print axioms SieveCert.rows22240R_792
