/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 740–750 of 5066

File 75 of 387: the parts `rows22240R_740` … `rows22240R_750` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 96624 in units of a depth-4 test: row 55 columns 50–50, row 55 columns
51–51, row 55 columns 52–52, row 55 columns 53–53, row 55 columns 54–54, row 55 columns 55–339, row 56 columns 0–14,
row 56 columns 15–19, row 56 columns 20–22, row 56 columns 23–24, row 56 columns 25–25), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_740 : rowsJ2 55 56 50 51 ≤ 3593251840051 := by decide +kernel

theorem rows22240R_741 : rowsJ2 55 56 51 52 ≤ 4727819356001 := by decide +kernel

theorem rows22240R_742 : rowsJ2 55 56 52 53 ≤ 6179468240028 := by decide +kernel

theorem rows22240R_743 : rowsJ2 55 56 53 54 ≤ 7648738758724 := by decide +kernel

theorem rows22240R_744 : rowsJ2 55 56 54 55 ≤ 9131057234929 := by decide +kernel

theorem rows22240R_745 : rowsJ2 55 56 55 340 ≤ 10769608231637 := by decide +kernel

theorem rows22240R_746 : rowsJ2 56 57 0 15 ≤ 2502485223645 := by decide +kernel

theorem rows22240R_747 : rowsJ2 56 57 15 20 ≤ 1952481660039 := by decide +kernel

theorem rows22240R_748 : rowsJ2 56 57 20 23 ≤ 700631818963 := by decide +kernel

theorem rows22240R_749 : rowsJ2 56 57 23 25 ≤ 314732372901 := by decide +kernel

theorem rows22240R_750 : rowsJ2 56 57 25 26 ≤ 120813845601 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_740
#print axioms SieveCert.rows22240R_750
