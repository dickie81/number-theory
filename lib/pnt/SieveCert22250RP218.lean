/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2342–2354 of 5796

File 218 of 465: the parts `rows22250R_2342` … `rows22250R_2354` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95952 tests: row 89 columns 67–68, row 89 columns 69–70, row 89 columns
71–72, row 89 columns 73–75, row 89 columns 76–78, row 89 columns 79–81, row 89 columns 82–83, row 89 columns 84–84,
row 89 columns 85–85, row 89 columns 86–86, row 89 columns 87–87, row 89 columns 88–88, row 89 columns 89–359), each
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

theorem rows22250R_2342 : rowsJ2 89 90 67 69 ≤ 0 := by decide +kernel

theorem rows22250R_2343 : rowsJ2 89 90 69 71 ≤ 0 := by decide +kernel

theorem rows22250R_2344 : rowsJ2 89 90 71 73 ≤ 0 := by decide +kernel

theorem rows22250R_2345 : rowsJ2 89 90 73 76 ≤ 0 := by decide +kernel

theorem rows22250R_2346 : rowsJ2 89 90 76 79 ≤ 0 := by decide +kernel

theorem rows22250R_2347 : rowsJ2 89 90 79 82 ≤ 221047038831 := by decide +kernel

theorem rows22250R_2348 : rowsJ2 89 90 82 84 ≤ 1016318699960 := by decide +kernel

theorem rows22250R_2349 : rowsJ2 89 90 84 85 ≤ 972561583446 := by decide +kernel

theorem rows22250R_2350 : rowsJ2 89 90 85 86 ≤ 1228196670061 := by decide +kernel

theorem rows22250R_2351 : rowsJ2 89 90 86 87 ≤ 1647873618256 := by decide +kernel

theorem rows22250R_2352 : rowsJ2 89 90 87 88 ≤ 2168971548303 := by decide +kernel

theorem rows22250R_2353 : rowsJ2 89 90 88 89 ≤ 2811088951841 := by decide +kernel

theorem rows22250R_2354 : rowsJ2 89 90 89 360 ≤ 3565682613718 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2342
#print axioms SieveCert.rows22250R_2354
