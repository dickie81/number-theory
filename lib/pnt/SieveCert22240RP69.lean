/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 678–688 of 5066

File 69 of 387: the parts `rows22240R_678` … `rows22240R_688` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 97687 in units of a depth-4 test: row 54 columns 15–19, row 54 columns
20–22, row 54 columns 23–24, row 54 columns 25–25, row 54 columns 26–26, row 54 columns 27–27, row 54 columns 28–28,
row 54 columns 29–29, row 54 columns 30–30, row 54 columns 31–31, row 54 columns 32–32), each a sum of refined costs
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

theorem rows22240R_678 : rowsJ2 54 55 15 20 ≤ 2364383931110 := by decide +kernel

theorem rows22240R_679 : rowsJ2 54 55 20 23 ≤ 917008301333 := by decide +kernel

theorem rows22240R_680 : rowsJ2 54 55 23 25 ≤ 427827561930 := by decide +kernel

theorem rows22240R_681 : rowsJ2 54 55 25 26 ≤ 168185196306 := by decide +kernel

theorem rows22240R_682 : rowsJ2 54 55 26 27 ≤ 144454409663 := by decide +kernel

theorem rows22240R_683 : rowsJ2 54 55 27 28 ≤ 123159186125 := by decide +kernel

theorem rows22240R_684 : rowsJ2 54 55 28 29 ≤ 106911894615 := by decide +kernel

theorem rows22240R_685 : rowsJ2 54 55 29 30 ≤ 87548745257 := by decide +kernel

theorem rows22240R_686 : rowsJ2 54 55 30 31 ≤ 70446170766 := by decide +kernel

theorem rows22240R_687 : rowsJ2 54 55 31 32 ≤ 52330872792 := by decide +kernel

theorem rows22240R_688 : rowsJ2 54 55 32 33 ≤ 39249185968 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_678
#print axioms SieveCert.rows22240R_688
