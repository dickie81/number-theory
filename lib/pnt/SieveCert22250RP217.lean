/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2687–2703 of 4715

File 217 of 351: the parts `rows22250R_2687` … `rows22250R_2703` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 92390 in units of a depth-4 test: row 101 columns 96–96, row 101
columns 97–97, row 101 columns 98–98, row 101 columns 99–99, row 101 columns 100–100, row 101 columns 101–339, row
102 columns 0–19, row 102 columns 20–30, row 102 columns 31–33, row 102 columns 34–35, row 102 columns 36–36, row
102 columns 37–37, row 102 columns 38–38, row 102 columns 39–39, row 102 columns 40–40, row 102 columns 41–41, row
102 columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2687 : rowsJ2 101 102 96 97 ≤ 5687442875551 := by decide +kernel

theorem rows22250R_2688 : rowsJ2 101 102 97 98 ≤ 6569858028109 := by decide +kernel

theorem rows22250R_2689 : rowsJ2 101 102 98 99 ≤ 7559079686908 := by decide +kernel

theorem rows22250R_2690 : rowsJ2 101 102 99 100 ≤ 8625672337823 := by decide +kernel

theorem rows22250R_2691 : rowsJ2 101 102 100 101 ≤ 9805265345737 := by decide +kernel

theorem rows22250R_2692 : rowsJ2 101 102 101 340 ≤ 11067793595290 := by decide +kernel

theorem rows22250R_2693 : rowsJ2 102 103 0 20 ≤ 0 := by decide +kernel

theorem rows22250R_2694 : rowsJ2 102 103 20 31 ≤ 2440059033468 := by decide +kernel

theorem rows22250R_2695 : rowsJ2 102 103 31 34 ≤ 12231962999108 := by decide +kernel

theorem rows22250R_2696 : rowsJ2 102 103 34 36 ≤ 16653291120688 := by decide +kernel

theorem rows22250R_2697 : rowsJ2 102 103 36 37 ≤ 11260450227551 := by decide +kernel

theorem rows22250R_2698 : rowsJ2 102 103 37 38 ≤ 13453864388877 := by decide +kernel

theorem rows22250R_2699 : rowsJ2 102 103 38 39 ≤ 15199262525593 := by decide +kernel

theorem rows22250R_2700 : rowsJ2 102 103 39 40 ≤ 15022592953150 := by decide +kernel

theorem rows22250R_2701 : rowsJ2 102 103 40 41 ≤ 12990109387718 := by decide +kernel

theorem rows22250R_2702 : rowsJ2 102 103 41 42 ≤ 11157579200726 := by decide +kernel

theorem rows22250R_2703 : rowsJ2 102 103 42 43 ≤ 9520026992311 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2687
#print axioms SieveCert.rows22250R_2703
