/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 252–264 of 5066

File 19 of 387: the parts `rows22240R_252` … `rows22240R_264` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99755 in units of a depth-4 test: row 37 columns 37–339, row 38 columns
0–13, row 38 columns 14–16, row 38 columns 17–18, row 38 columns 19–20, row 38 columns 21–22, row 38 columns 23–24,
row 38 columns 25–25, row 38 columns 26–26, row 38 columns 27–27, row 38 columns 28–28, row 38 columns 29–29, row 38
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

theorem rows22240R_252 : rowsJ2 37 38 37 340 ≤ 843445877498 := by decide +kernel

theorem rows22240R_253 : rowsJ2 38 39 0 14 ≤ 703362547882 := by decide +kernel

theorem rows22240R_254 : rowsJ2 38 39 14 17 ≤ 1858311582085 := by decide +kernel

theorem rows22240R_255 : rowsJ2 38 39 17 19 ≤ 2010356498209 := by decide +kernel

theorem rows22240R_256 : rowsJ2 38 39 19 21 ≤ 2290290757129 := by decide +kernel

theorem rows22240R_257 : rowsJ2 38 39 21 23 ≤ 2353581855558 := by decide +kernel

theorem rows22240R_258 : rowsJ2 38 39 23 25 ≤ 2189488457938 := by decide +kernel

theorem rows22240R_259 : rowsJ2 38 39 25 26 ≤ 1000380806853 := by decide +kernel

theorem rows22240R_260 : rowsJ2 38 39 26 27 ≤ 926944205250 := by decide +kernel

theorem rows22240R_261 : rowsJ2 38 39 27 28 ≤ 846882431695 := by decide +kernel

theorem rows22240R_262 : rowsJ2 38 39 28 29 ≤ 783951634713 := by decide +kernel

theorem rows22240R_263 : rowsJ2 38 39 29 30 ≤ 731257296171 := by decide +kernel

theorem rows22240R_264 : rowsJ2 38 39 30 31 ≤ 703828168037 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_252
#print axioms SieveCert.rows22240R_264
