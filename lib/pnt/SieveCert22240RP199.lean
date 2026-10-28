/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2297–2305 of 5066

File 199 of 387: the parts `rows22240R_2297` … `rows22240R_2305` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 98345 in units of a depth-4 test: row 89 columns 86–86, row 89 columns
87–87, row 89 columns 88–88, row 89 columns 89–339, row 90 columns 0–16, row 90 columns 17–19, row 90 columns 20–22,
row 90 columns 23–26, row 90 columns 27–32), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22240R_2297 : rowsJ2 89 90 86 87 ≤ 6217101928225 := by decide +kernel

theorem rows22240R_2298 : rowsJ2 89 90 87 88 ≤ 7704079948790 := by decide +kernel

theorem rows22240R_2299 : rowsJ2 89 90 88 89 ≤ 9117239620097 := by decide +kernel

theorem rows22240R_2300 : rowsJ2 89 90 89 340 ≤ 9264216039300 := by decide +kernel

theorem rows22240R_2301 : rowsJ2 90 91 0 17 ≤ 5227276866 := by decide +kernel

theorem rows22240R_2302 : rowsJ2 90 91 17 20 ≤ 0 := by decide +kernel

theorem rows22240R_2303 : rowsJ2 90 91 20 23 ≤ 0 := by decide +kernel

theorem rows22240R_2304 : rowsJ2 90 91 23 27 ≤ 0 := by decide +kernel

theorem rows22240R_2305 : rowsJ2 90 91 27 33 ≤ 195227483253 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2297
#print axioms SieveCert.rows22240R_2305
