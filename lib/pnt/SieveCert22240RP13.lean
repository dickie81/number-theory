/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 191–200 of 5066

File 13 of 387: the parts `rows22240R_191` … `rows22240R_200` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 97272 in units of a depth-4 test: row 34 columns 28–28, row 34 columns
29–29, row 34 columns 30–30, row 34 columns 31–31, row 34 columns 32–32, row 34 columns 33–33, row 34 columns
34–339, row 35 columns 0–13, row 35 columns 14–16, row 35 columns 17–18), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_191 : rowsJ2 34 35 28 29 ≤ 1101062323743 := by decide +kernel

theorem rows22240R_192 : rowsJ2 34 35 29 30 ≤ 1024999001963 := by decide +kernel

theorem rows22240R_193 : rowsJ2 34 35 30 31 ≤ 964390659191 := by decide +kernel

theorem rows22240R_194 : rowsJ2 34 35 31 32 ≤ 922677310699 := by decide +kernel

theorem rows22240R_195 : rowsJ2 34 35 32 33 ≤ 912614995556 := by decide +kernel

theorem rows22240R_196 : rowsJ2 34 35 33 34 ≤ 944842139923 := by decide +kernel

theorem rows22240R_197 : rowsJ2 34 35 34 340 ≤ 1020307878553 := by decide +kernel

theorem rows22240R_198 : rowsJ2 35 36 0 14 ≤ 738941978307 := by decide +kernel

theorem rows22240R_199 : rowsJ2 35 36 14 17 ≤ 1614837673737 := by decide +kernel

theorem rows22240R_200 : rowsJ2 35 36 17 19 ≤ 1984799154800 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_191
#print axioms SieveCert.rows22240R_200
