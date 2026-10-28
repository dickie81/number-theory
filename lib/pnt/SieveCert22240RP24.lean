/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 293–305 of 5066

File 24 of 387: the parts `rows22240R_293` … `rows22240R_305` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 98092 in units of a depth-4 test: row 39 columns 39–339, row 40 columns
0–13, row 40 columns 14–16, row 40 columns 17–18, row 40 columns 19–20, row 40 columns 21–22, row 40 columns 23–24,
row 40 columns 25–25, row 40 columns 26–26, row 40 columns 27–27, row 40 columns 28–28, row 40 columns 29–29, row 40
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

theorem rows22240R_293 : rowsJ2 39 40 39 340 ≤ 481849493379 := by decide +kernel

theorem rows22240R_294 : rowsJ2 40 41 0 14 ≤ 757503248888 := by decide +kernel

theorem rows22240R_295 : rowsJ2 40 41 14 17 ≤ 2006217512779 := by decide +kernel

theorem rows22240R_296 : rowsJ2 40 41 17 19 ≤ 1966093189717 := by decide +kernel

theorem rows22240R_297 : rowsJ2 40 41 19 21 ≤ 2152954041053 := by decide +kernel

theorem rows22240R_298 : rowsJ2 40 41 21 23 ≤ 2108729977873 := by decide +kernel

theorem rows22240R_299 : rowsJ2 40 41 23 25 ≤ 1900675315894 := by decide +kernel

theorem rows22240R_300 : rowsJ2 40 41 25 26 ≤ 846500962992 := by decide +kernel

theorem rows22240R_301 : rowsJ2 40 41 26 27 ≤ 773948858140 := by decide +kernel

theorem rows22240R_302 : rowsJ2 40 41 27 28 ≤ 704982435911 := by decide +kernel

theorem rows22240R_303 : rowsJ2 40 41 28 29 ≤ 652913786636 := by decide +kernel

theorem rows22240R_304 : rowsJ2 40 41 29 30 ≤ 610701739697 := by decide +kernel

theorem rows22240R_305 : rowsJ2 40 41 30 31 ≤ 588959264451 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_293
#print axioms SieveCert.rows22240R_305
