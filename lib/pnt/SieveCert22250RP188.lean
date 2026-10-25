/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2265–2277 of 4715

File 188 of 351: the parts `rows22250R_2265` … `rows22250R_2277` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96564 tests: row 91 columns 90–90, row 91 columns 91–339, row 92 columns
0–15, row 92 columns 16–20, row 92 columns 21–28, row 92 columns 29–33, row 92 columns 34–36, row 92 columns 37–38,
row 92 columns 39–39, row 92 columns 40–40, row 92 columns 41–41, row 92 columns 42–42, row 92 columns 43–43), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2265 : rowsJ2 91 92 90 91 ≤ 4505098222281 := by decide +kernel

theorem rows22250R_2266 : rowsJ2 91 92 91 340 ≤ 4385603423706 := by decide +kernel

theorem rows22250R_2267 : rowsJ2 92 93 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2268 : rowsJ2 92 93 16 21 ≤ 0 := by decide +kernel

theorem rows22250R_2269 : rowsJ2 92 93 21 29 ≤ 0 := by decide +kernel

theorem rows22250R_2270 : rowsJ2 92 93 29 34 ≤ 4001627685376 := by decide +kernel

theorem rows22250R_2271 : rowsJ2 92 93 34 37 ≤ 13316770629293 := by decide +kernel

theorem rows22250R_2272 : rowsJ2 92 93 37 39 ≤ 16241020932089 := by decide +kernel

theorem rows22250R_2273 : rowsJ2 92 93 39 40 ≤ 10147206276800 := by decide +kernel

theorem rows22250R_2274 : rowsJ2 92 93 40 41 ≤ 11658431657607 := by decide +kernel

theorem rows22250R_2275 : rowsJ2 92 93 41 42 ≤ 13282385934492 := by decide +kernel

theorem rows22250R_2276 : rowsJ2 92 93 42 43 ≤ 14850354039425 := by decide +kernel

theorem rows22250R_2277 : rowsJ2 92 93 43 44 ≤ 16188586970251 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2265
#print axioms SieveCert.rows22250R_2277
