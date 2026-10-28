/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2344–2355 of 5066

File 203 of 387: the parts `rows22240R_2344` … `rows22240R_2355` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 94705 in units of a depth-4 test: row 90 columns 89–89, row 90 columns
90–339, row 91 columns 0–16, row 91 columns 17–19, row 91 columns 20–23, row 91 columns 24–28, row 91 columns 29–33,
row 91 columns 34–36, row 91 columns 37–38, row 91 columns 39–39, row 91 columns 40–40, row 91 columns 41–41), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2344 : rowsJ2 90 91 89 90 ≤ 7948069305383 := by decide +kernel

theorem rows22240R_2345 : rowsJ2 90 91 90 340 ≤ 7137288850503 := by decide +kernel

theorem rows22240R_2346 : rowsJ2 91 92 0 17 ≤ 0 := by decide +kernel

theorem rows22240R_2347 : rowsJ2 91 92 17 20 ≤ 0 := by decide +kernel

theorem rows22240R_2348 : rowsJ2 91 92 20 24 ≤ 0 := by decide +kernel

theorem rows22240R_2349 : rowsJ2 91 92 24 29 ≤ 0 := by decide +kernel

theorem rows22240R_2350 : rowsJ2 91 92 29 34 ≤ 1568273335200 := by decide +kernel

theorem rows22240R_2351 : rowsJ2 91 92 34 37 ≤ 9416479462518 := by decide +kernel

theorem rows22240R_2352 : rowsJ2 91 92 37 39 ≤ 12956928801322 := by decide +kernel

theorem rows22240R_2353 : rowsJ2 91 92 39 40 ≤ 8323416773524 := by decide +kernel

theorem rows22240R_2354 : rowsJ2 91 92 40 41 ≤ 9582951981029 := by decide +kernel

theorem rows22240R_2355 : rowsJ2 91 92 41 42 ≤ 10860469273844 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2344
#print axioms SieveCert.rows22240R_2355
