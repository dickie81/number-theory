/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 219–230 of 5796

File 15 of 465: the parts `rows22250R_219` … `rows22250R_230` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 89522 tests: row 36 columns 19–20, row 36 columns 21–22, row 36 columns
23–24, row 36 columns 25–25, row 36 columns 26–26, row 36 columns 27–27, row 36 columns 28–28, row 36 columns 29–29,
row 36 columns 30–30, row 36 columns 31–31, row 36 columns 32–32, row 36 columns 33–33), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_219 : rowsJ2 36 37 19 21 ≤ 1923863209041 := by decide +kernel

theorem rows22250R_220 : rowsJ2 36 37 21 23 ≤ 2041780688772 := by decide +kernel

theorem rows22250R_221 : rowsJ2 36 37 23 25 ≤ 1978708596416 := by decide +kernel

theorem rows22250R_222 : rowsJ2 36 37 25 26 ≤ 920989023439 := by decide +kernel

theorem rows22250R_223 : rowsJ2 36 37 26 27 ≤ 866564887316 := by decide +kernel

theorem rows22250R_224 : rowsJ2 36 37 27 28 ≤ 802031682450 := by decide +kernel

theorem rows22250R_225 : rowsJ2 36 37 28 29 ≤ 735935301290 := by decide +kernel

theorem rows22250R_226 : rowsJ2 36 37 29 30 ≤ 675321587030 := by decide +kernel

theorem rows22250R_227 : rowsJ2 36 37 30 31 ≤ 628257147554 := by decide +kernel

theorem rows22250R_228 : rowsJ2 36 37 31 32 ≤ 591788959592 := by decide +kernel

theorem rows22250R_229 : rowsJ2 36 37 32 33 ≤ 576883741405 := by decide +kernel

theorem rows22250R_230 : rowsJ2 36 37 33 34 ≤ 587145006418 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_219
#print axioms SieveCert.rows22250R_230
