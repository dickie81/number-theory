/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2437–2449 of 5796

File 225 of 465: the parts `rows22250R_2437` … `rows22250R_2449` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 90783 tests: row 91 columns 67–68, row 91 columns 69–70, row 91 columns
71–73, row 91 columns 74–77, row 91 columns 78–80, row 91 columns 81–82, row 91 columns 83–83, row 91 columns 84–84,
row 91 columns 85–85, row 91 columns 86–86, row 91 columns 87–87, row 91 columns 88–88, row 91 columns 89–89), each
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

theorem rows22250R_2437 : rowsJ2 91 92 67 69 ≤ 0 := by decide +kernel

theorem rows22250R_2438 : rowsJ2 91 92 69 71 ≤ 0 := by decide +kernel

theorem rows22250R_2439 : rowsJ2 91 92 71 74 ≤ 0 := by decide +kernel

theorem rows22250R_2440 : rowsJ2 91 92 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_2441 : rowsJ2 91 92 78 81 ≤ 54644819198 := by decide +kernel

theorem rows22250R_2442 : rowsJ2 91 92 81 83 ≤ 502388214021 := by decide +kernel

theorem rows22250R_2443 : rowsJ2 91 92 83 84 ≤ 567910185316 := by decide +kernel

theorem rows22250R_2444 : rowsJ2 91 92 84 85 ≤ 863200124001 := by decide +kernel

theorem rows22250R_2445 : rowsJ2 91 92 85 86 ≤ 1210750538917 := by decide +kernel

theorem rows22250R_2446 : rowsJ2 91 92 86 87 ≤ 1623367473513 := by decide +kernel

theorem rows22250R_2447 : rowsJ2 91 92 87 88 ≤ 2140549462804 := by decide +kernel

theorem rows22250R_2448 : rowsJ2 91 92 88 89 ≤ 2779880135263 := by decide +kernel

theorem rows22250R_2449 : rowsJ2 91 92 89 90 ≤ 3534690592951 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2437
#print axioms SieveCert.rows22250R_2449
