/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 275–286 of 4715

File 23 of 351: the parts `rows22250R_275` … `rows22250R_286` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 93308 in units of a depth-4 test: row 39 columns 39–339, row 40 columns
0–13, row 40 columns 14–16, row 40 columns 17–19, row 40 columns 20–22, row 40 columns 23–24, row 40 columns 25–25,
row 40 columns 26–26, row 40 columns 27–27, row 40 columns 28–28, row 40 columns 29–29, row 40 columns 30–30), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_275 : rowsJ2 39 40 39 340 ≤ 283307413584 := by decide +kernel

theorem rows22250R_276 : rowsJ2 40 41 0 14 ≤ 1269201471682 := by decide +kernel

theorem rows22250R_277 : rowsJ2 40 41 14 17 ≤ 2389896945835 := by decide +kernel

theorem rows22250R_278 : rowsJ2 40 41 17 20 ≤ 2835901174464 := by decide +kernel

theorem rows22250R_279 : rowsJ2 40 41 20 23 ≤ 2524808253809 := by decide +kernel

theorem rows22250R_280 : rowsJ2 40 41 23 25 ≤ 1368401860215 := by decide +kernel

theorem rows22250R_281 : rowsJ2 40 41 25 26 ≤ 589413716283 := by decide +kernel

theorem rows22250R_282 : rowsJ2 40 41 26 27 ≤ 531936067926 := by decide +kernel

theorem rows22250R_283 : rowsJ2 40 41 27 28 ≤ 484016497063 := by decide +kernel

theorem rows22250R_284 : rowsJ2 40 41 28 29 ≤ 448111786626 := by decide +kernel

theorem rows22250R_285 : rowsJ2 40 41 29 30 ≤ 433280353969 := by decide +kernel

theorem rows22250R_286 : rowsJ2 40 41 30 31 ≤ 441128821793 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_275
#print axioms SieveCert.rows22250R_286
