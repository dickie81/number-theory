/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2586–2602 of 4715

File 211 of 351: the parts `rows22250R_2586` … `rows22250R_2602` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99093 tests: row 99 columns 80–80, row 99 columns 81–81, row 99 columns
82–82, row 99 columns 83–83, row 99 columns 84–84, row 99 columns 85–85, row 99 columns 86–86, row 99 columns 87–87,
row 99 columns 88–88, row 99 columns 89–89, row 99 columns 90–90, row 99 columns 91–91, row 99 columns 92–92, row 99
columns 93–93, row 99 columns 94–94, row 99 columns 95–95, row 99 columns 96–96), each a sum of refined costs
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

theorem rows22250R_2586 : rowsJ2 99 100 80 81 ≤ 1100978645348 := by decide +kernel

theorem rows22250R_2587 : rowsJ2 99 100 81 82 ≤ 1521958460139 := by decide +kernel

theorem rows22250R_2588 : rowsJ2 99 100 82 83 ≤ 2002859748755 := by decide +kernel

theorem rows22250R_2589 : rowsJ2 99 100 83 84 ≤ 2190810101115 := by decide +kernel

theorem rows22250R_2590 : rowsJ2 99 100 84 85 ≤ 2024716680398 := by decide +kernel

theorem rows22250R_2591 : rowsJ2 99 100 85 86 ≤ 1871828500333 := by decide +kernel

theorem rows22250R_2592 : rowsJ2 99 100 86 87 ≤ 1756590175937 := by decide +kernel

theorem rows22250R_2593 : rowsJ2 99 100 87 88 ≤ 1735251119656 := by decide +kernel

theorem rows22250R_2594 : rowsJ2 99 100 88 89 ≤ 1793244143909 := by decide +kernel

theorem rows22250R_2595 : rowsJ2 99 100 89 90 ≤ 1949460452714 := by decide +kernel

theorem rows22250R_2596 : rowsJ2 99 100 90 91 ≤ 2190817922947 := by decide +kernel

theorem rows22250R_2597 : rowsJ2 99 100 91 92 ≤ 2489854547520 := by decide +kernel

theorem rows22250R_2598 : rowsJ2 99 100 92 93 ≤ 2877176242535 := by decide +kernel

theorem rows22250R_2599 : rowsJ2 99 100 93 94 ≤ 3326264931109 := by decide +kernel

theorem rows22250R_2600 : rowsJ2 99 100 94 95 ≤ 3867445596372 := by decide +kernel

theorem rows22250R_2601 : rowsJ2 99 100 95 96 ≤ 4473635834545 := by decide +kernel

theorem rows22250R_2602 : rowsJ2 99 100 96 97 ≤ 5176263781599 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2586
#print axioms SieveCert.rows22250R_2602
