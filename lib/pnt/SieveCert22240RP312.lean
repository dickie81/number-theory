/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3947–3957 of 5066

File 312 of 387: the parts `rows22240R_3947` … `rows22240R_3957` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 99271 in units of a depth-4 test: row 137 columns 60–60, row 137
columns 61–61, row 137 columns 62–62, row 137 columns 63–63, row 137 columns 64–64, row 137 columns 65–65, row 137
columns 66–66, row 137 columns 67–67, row 137 columns 68–68, row 137 columns 69–69, row 137 columns 70–70), each a
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

theorem rows22240R_3947 : rowsJ2 137 138 60 61 ≤ 8437371286194 := by decide +kernel

theorem rows22240R_3948 : rowsJ2 137 138 61 62 ≤ 9343020734968 := by decide +kernel

theorem rows22240R_3949 : rowsJ2 137 138 62 63 ≤ 10204121493051 := by decide +kernel

theorem rows22240R_3950 : rowsJ2 137 138 63 64 ≤ 10999954757827 := by decide +kernel

theorem rows22240R_3951 : rowsJ2 137 138 64 65 ≤ 11750803198907 := by decide +kernel

theorem rows22240R_3952 : rowsJ2 137 138 65 66 ≤ 11517470392973 := by decide +kernel

theorem rows22240R_3953 : rowsJ2 137 138 66 67 ≤ 10411626007184 := by decide +kernel

theorem rows22240R_3954 : rowsJ2 137 138 67 68 ≤ 9359028179336 := by decide +kernel

theorem rows22240R_3955 : rowsJ2 137 138 68 69 ≤ 8378793289715 := by decide +kernel

theorem rows22240R_3956 : rowsJ2 137 138 69 70 ≤ 7447841270481 := by decide +kernel

theorem rows22240R_3957 : rowsJ2 137 138 70 71 ≤ 6585755236737 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3947
#print axioms SieveCert.rows22240R_3957
