/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3017–3033 of 5066

File 250 of 387: the parts `rows22240R_3017` … `rows22240R_3033` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 99610 in units of a depth-4 test: row 105 columns 92–93, row 105
columns 94–94, row 105 columns 95–95, row 105 columns 96–96, row 105 columns 97–97, row 105 columns 98–98, row 105
columns 99–99, row 105 columns 100–100, row 105 columns 101–101, row 105 columns 102–339, row 106 columns 0–19, row
106 columns 20–30, row 106 columns 31–33, row 106 columns 34–35, row 106 columns 36–36, row 106 columns 37–37, row
106 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3017 : rowsJ2 105 106 92 94 ≤ 9022520392189 := by decide +kernel

theorem rows22240R_3018 : rowsJ2 105 106 94 95 ≤ 5745189589901 := by decide +kernel

theorem rows22240R_3019 : rowsJ2 105 106 95 96 ≤ 6664912500808 := by decide +kernel

theorem rows22240R_3020 : rowsJ2 105 106 96 97 ≤ 7710018703101 := by decide +kernel

theorem rows22240R_3021 : rowsJ2 105 106 97 98 ≤ 8817368988308 := by decide +kernel

theorem rows22240R_3022 : rowsJ2 105 106 98 99 ≤ 10056894470941 := by decide +kernel

theorem rows22240R_3023 : rowsJ2 105 106 99 100 ≤ 11364334578975 := by decide +kernel

theorem rows22240R_3024 : rowsJ2 105 106 100 101 ≤ 12794603790840 := by decide +kernel

theorem rows22240R_3025 : rowsJ2 105 106 101 102 ≤ 14298834113313 := by decide +kernel

theorem rows22240R_3026 : rowsJ2 105 106 102 340 ≤ 388616332620659 := by decide +kernel

theorem rows22240R_3027 : rowsJ2 106 107 0 20 ≤ 0 := by decide +kernel

theorem rows22240R_3028 : rowsJ2 106 107 20 31 ≤ 3196507855913 := by decide +kernel

theorem rows22240R_3029 : rowsJ2 106 107 31 34 ≤ 13354531094595 := by decide +kernel

theorem rows22240R_3030 : rowsJ2 106 107 34 36 ≤ 17627659908789 := by decide +kernel

theorem rows22240R_3031 : rowsJ2 106 107 36 37 ≤ 11716848711487 := by decide +kernel

theorem rows22240R_3032 : rowsJ2 106 107 37 38 ≤ 14119684715982 := by decide +kernel

theorem rows22240R_3033 : rowsJ2 106 107 38 39 ≤ 15954793386376 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3017
#print axioms SieveCert.rows22240R_3033
