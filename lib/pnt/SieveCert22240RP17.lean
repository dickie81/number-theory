/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 233–245 of 5066

File 17 of 387: the parts `rows22240R_233` … `rows22240R_245` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99881 in units of a depth-4 test: row 36 columns 36–339, row 37 columns
0–13, row 37 columns 14–16, row 37 columns 17–18, row 37 columns 19–20, row 37 columns 21–22, row 37 columns 23–24,
row 37 columns 25–25, row 37 columns 26–26, row 37 columns 27–27, row 37 columns 28–28, row 37 columns 29–29, row 37
columns 30–30), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

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

theorem rows22240R_233 : rowsJ2 36 37 36 340 ≤ 949904653328 := by decide +kernel

theorem rows22240R_234 : rowsJ2 37 38 0 14 ≤ 693863273926 := by decide +kernel

theorem rows22240R_235 : rowsJ2 37 38 14 17 ≤ 1782728385935 := by decide +kernel

theorem rows22240R_236 : rowsJ2 37 38 17 19 ≤ 2012432851723 := by decide +kernel

theorem rows22240R_237 : rowsJ2 37 38 19 21 ≤ 2351827524092 := by decide +kernel

theorem rows22240R_238 : rowsJ2 37 38 21 23 ≤ 2461970145348 := by decide +kernel

theorem rows22240R_239 : rowsJ2 37 38 23 25 ≤ 2335091634224 := by decide +kernel

theorem rows22240R_240 : rowsJ2 37 38 25 26 ≤ 1079294364419 := by decide +kernel

theorem rows22240R_241 : rowsJ2 37 38 26 27 ≤ 1006041704074 := by decide +kernel

theorem rows22240R_242 : rowsJ2 37 38 27 28 ≤ 928587059460 := by decide +kernel

theorem rows22240R_243 : rowsJ2 37 38 28 29 ≤ 855369464217 := by decide +kernel

theorem rows22240R_244 : rowsJ2 37 38 29 30 ≤ 802163475314 := by decide +kernel

theorem rows22240R_245 : rowsJ2 37 38 30 31 ≤ 764830029255 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_233
#print axioms SieveCert.rows22240R_245
