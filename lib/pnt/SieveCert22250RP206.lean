/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2508–2522 of 4715

File 206 of 351: the parts `rows22250R_2508` … `rows22250R_2522` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 98639 in units of a depth-4 test: row 97 columns 86–86, row 97 columns
87–87, row 97 columns 88–88, row 97 columns 89–89, row 97 columns 90–90, row 97 columns 91–91, row 97 columns 92–92,
row 97 columns 93–93, row 97 columns 94–94, row 97 columns 95–95, row 97 columns 96–96, row 97 columns 97–339, row
98 columns 0–16, row 98 columns 17–27, row 98 columns 28–32), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2508 : rowsJ2 97 98 86 87 ≤ 2442953674891 := by decide +kernel

theorem rows22250R_2509 : rowsJ2 97 98 87 88 ≤ 2312739940995 := by decide +kernel

theorem rows22250R_2510 : rowsJ2 97 98 88 89 ≤ 2258765922261 := by decide +kernel

theorem rows22250R_2511 : rowsJ2 97 98 89 90 ≤ 2298501607308 := by decide +kernel

theorem rows22250R_2512 : rowsJ2 97 98 90 91 ≤ 2417029156483 := by decide +kernel

theorem rows22250R_2513 : rowsJ2 97 98 91 92 ≤ 2633731296943 := by decide +kernel

theorem rows22250R_2514 : rowsJ2 97 98 92 93 ≤ 2935162348914 := by decide +kernel

theorem rows22250R_2515 : rowsJ2 97 98 93 94 ≤ 3294393320006 := by decide +kernel

theorem rows22250R_2516 : rowsJ2 97 98 94 95 ≤ 3741619738116 := by decide +kernel

theorem rows22250R_2517 : rowsJ2 97 98 95 96 ≤ 4250860691199 := by decide +kernel

theorem rows22250R_2518 : rowsJ2 97 98 96 97 ≤ 4852028704283 := by decide +kernel

theorem rows22250R_2519 : rowsJ2 97 98 97 340 ≤ 5518584580515 := by decide +kernel

theorem rows22250R_2520 : rowsJ2 98 99 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2521 : rowsJ2 98 99 17 28 ≤ 0 := by decide +kernel

theorem rows22250R_2522 : rowsJ2 98 99 28 33 ≤ 4905659249913 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2508
#print axioms SieveCert.rows22250R_2522
