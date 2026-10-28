/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2344–2354 of 4715

File 194 of 351: the parts `rows22250R_2344` … `rows22250R_2354` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 98608 in units of a depth-4 test: row 93 columns 87–87, row 93 columns
88–88, row 93 columns 89–89, row 93 columns 90–90, row 93 columns 91–91, row 93 columns 92–92, row 93 columns
93–339, row 94 columns 0–15, row 94 columns 16–21, row 94 columns 22–30, row 94 columns 31–34), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2344 : rowsJ2 93 94 87 88 ≤ 4082066396352 := by decide +kernel

theorem rows22250R_2345 : rowsJ2 93 94 88 89 ≤ 3857792449066 := by decide +kernel

theorem rows22250R_2346 : rowsJ2 93 94 89 90 ≤ 3683474419852 := by decide +kernel

theorem rows22250R_2347 : rowsJ2 93 94 90 91 ≤ 3579414221058 := by decide +kernel

theorem rows22250R_2348 : rowsJ2 93 94 91 92 ≤ 3564973480711 := by decide +kernel

theorem rows22250R_2349 : rowsJ2 93 94 92 93 ≤ 3625678752780 := by decide +kernel

theorem rows22250R_2350 : rowsJ2 93 94 93 340 ≤ 3780018266096 := by decide +kernel

theorem rows22250R_2351 : rowsJ2 94 95 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2352 : rowsJ2 94 95 16 22 ≤ 0 := by decide +kernel

theorem rows22250R_2353 : rowsJ2 94 95 22 31 ≤ 420424910027 := by decide +kernel

theorem rows22250R_2354 : rowsJ2 94 95 31 35 ≤ 8485529465308 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2344
#print axioms SieveCert.rows22250R_2354
