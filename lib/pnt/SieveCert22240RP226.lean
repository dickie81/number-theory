/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2641–2653 of 5066

File 226 of 387: the parts `rows22240R_2641` … `rows22240R_2653` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 95632 in units of a depth-4 test: row 97 columns 57–59, row 97 columns
60–64, row 97 columns 65–70, row 97 columns 71–75, row 97 columns 76–78, row 97 columns 79–79, row 97 columns 80–80,
row 97 columns 81–81, row 97 columns 82–82, row 97 columns 83–83, row 97 columns 84–84, row 97 columns 85–85, row 97
columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2641 : rowsJ2 97 98 57 60 ≤ 83572932070 := by decide +kernel

theorem rows22240R_2642 : rowsJ2 97 98 60 65 ≤ 0 := by decide +kernel

theorem rows22240R_2643 : rowsJ2 97 98 65 71 ≤ 0 := by decide +kernel

theorem rows22240R_2644 : rowsJ2 97 98 71 76 ≤ 0 := by decide +kernel

theorem rows22240R_2645 : rowsJ2 97 98 76 79 ≤ 608591284855 := by decide +kernel

theorem rows22240R_2646 : rowsJ2 97 98 79 80 ≤ 620180500053 := by decide +kernel

theorem rows22240R_2647 : rowsJ2 97 98 80 81 ≤ 943027380369 := by decide +kernel

theorem rows22240R_2648 : rowsJ2 97 98 81 82 ≤ 1407973103430 := by decide +kernel

theorem rows22240R_2649 : rowsJ2 97 98 82 83 ≤ 2041730686736 := by decide +kernel

theorem rows22240R_2650 : rowsJ2 97 98 83 84 ≤ 2841612387034 := by decide +kernel

theorem rows22240R_2651 : rowsJ2 97 98 84 85 ≤ 3537586042093 := by decide +kernel

theorem rows22240R_2652 : rowsJ2 97 98 85 86 ≤ 3484907774348 := by decide +kernel

theorem rows22240R_2653 : rowsJ2 97 98 86 87 ≤ 2922389826536 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2641
#print axioms SieveCert.rows22240R_2653
