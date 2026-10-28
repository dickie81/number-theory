/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 271–281 of 5066

File 21 of 387: the parts `rows22240R_271` … `rows22240R_281` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 96317 in units of a depth-4 test: row 38 columns 37–37, row 38 columns
38–339, row 39 columns 0–13, row 39 columns 14–16, row 39 columns 17–18, row 39 columns 19–20, row 39 columns 21–22,
row 39 columns 23–24, row 39 columns 25–25, row 39 columns 26–26, row 39 columns 27–27), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22240R_271 : rowsJ2 38 39 37 38 ≤ 713490379139 := by decide +kernel

theorem rows22240R_272 : rowsJ2 38 39 38 340 ≤ 664235115748 := by decide +kernel

theorem rows22240R_273 : rowsJ2 39 40 0 14 ≤ 724075223918 := by decide +kernel

theorem rows22240R_274 : rowsJ2 39 40 14 17 ≤ 1931644703255 := by decide +kernel

theorem rows22240R_275 : rowsJ2 39 40 17 19 ≤ 1994252806874 := by decide +kernel

theorem rows22240R_276 : rowsJ2 39 40 19 21 ≤ 2225392384040 := by decide +kernel

theorem rows22240R_277 : rowsJ2 39 40 21 23 ≤ 2233834948627 := by decide +kernel

theorem rows22240R_278 : rowsJ2 39 40 23 25 ≤ 2044732388399 := by decide +kernel

theorem rows22240R_279 : rowsJ2 39 40 25 26 ≤ 924758645336 := by decide +kernel

theorem rows22240R_280 : rowsJ2 39 40 26 27 ≤ 845250419264 := by decide +kernel

theorem rows22240R_281 : rowsJ2 39 40 27 28 ≤ 775574768085 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_271
#print axioms SieveCert.rows22240R_281
