/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 201–213 of 5066

File 14 of 387: the parts `rows22240R_201` … `rows22240R_213` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 98222 in units of a depth-4 test: row 35 columns 19–20, row 35 columns
21–22, row 35 columns 23–23, row 35 columns 24–24, row 35 columns 25–25, row 35 columns 26–26, row 35 columns 27–27,
row 35 columns 28–28, row 35 columns 29–29, row 35 columns 30–30, row 35 columns 31–31, row 35 columns 32–32, row 35
columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_201 : rowsJ2 35 36 19 21 ≤ 2462976460524 := by decide +kernel

theorem rows22240R_202 : rowsJ2 35 36 21 23 ≤ 2649091515271 := by decide +kernel

theorem rows22240R_203 : rowsJ2 35 36 23 24 ≤ 1332604872425 := by decide +kernel

theorem rows22240R_204 : rowsJ2 35 36 24 25 ≤ 1290715365211 := by decide +kernel

theorem rows22240R_205 : rowsJ2 35 36 25 26 ≤ 1235625807803 := by decide +kernel

theorem rows22240R_206 : rowsJ2 35 36 26 27 ≤ 1167775690801 := by decide +kernel

theorem rows22240R_207 : rowsJ2 35 36 27 28 ≤ 1094427274695 := by decide +kernel

theorem rows22240R_208 : rowsJ2 35 36 28 29 ≤ 1015042842737 := by decide +kernel

theorem rows22240R_209 : rowsJ2 35 36 29 30 ≤ 944867614242 := by decide +kernel

theorem rows22240R_210 : rowsJ2 35 36 30 31 ≤ 890878358562 := by decide +kernel

theorem rows22240R_211 : rowsJ2 35 36 31 32 ≤ 860783914853 := by decide +kernel

theorem rows22240R_212 : rowsJ2 35 36 32 33 ≤ 863175882490 := by decide +kernel

theorem rows22240R_213 : rowsJ2 35 36 33 34 ≤ 905260923177 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_201
#print axioms SieveCert.rows22240R_213
