/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 274–285 of 5796

File 21 of 465: the parts `rows22250R_274` … `rows22250R_285` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 88067 tests: row 39 columns 14–16, row 39 columns 17–18, row 39 columns
19–20, row 39 columns 21–22, row 39 columns 23–24, row 39 columns 25–26, row 39 columns 27–27, row 39 columns 28–28,
row 39 columns 29–29, row 39 columns 30–30, row 39 columns 31–31, row 39 columns 32–32), each a sum of refined costs
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

theorem rows22250R_274 : rowsJ2 39 40 14 17 ≤ 1540259236836 := by decide +kernel

theorem rows22250R_275 : rowsJ2 39 40 17 19 ≤ 1590403500674 := by decide +kernel

theorem rows22250R_276 : rowsJ2 39 40 19 21 ≤ 1773987328083 := by decide +kernel

theorem rows22250R_277 : rowsJ2 39 40 21 23 ≤ 1779607614293 := by decide +kernel

theorem rows22250R_278 : rowsJ2 39 40 23 25 ≤ 1627847703219 := by decide +kernel

theorem rows22250R_279 : rowsJ2 39 40 25 27 ≤ 1407671206691 := by decide +kernel

theorem rows22250R_280 : rowsJ2 39 40 27 28 ≤ 613645749722 := by decide +kernel

theorem rows22250R_281 : rowsJ2 39 40 28 29 ≤ 559801681338 := by decide +kernel

theorem rows22250R_282 : rowsJ2 39 40 29 30 ≤ 520109789651 := by decide +kernel

theorem rows22250R_283 : rowsJ2 39 40 30 31 ≤ 488768398259 := by decide +kernel

theorem rows22250R_284 : rowsJ2 39 40 31 32 ≤ 472186284610 := by decide +kernel

theorem rows22250R_285 : rowsJ2 39 40 32 33 ≤ 477072104062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_274
#print axioms SieveCert.rows22250R_285
