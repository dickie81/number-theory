/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2667–2683 of 5066

File 228 of 387: the parts `rows22240R_2667` … `rows22240R_2683` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 99057 in units of a depth-4 test: row 98 columns 22–30, row 98 columns
31–34, row 98 columns 35–36, row 98 columns 37–37, row 98 columns 38–38, row 98 columns 39–39, row 98 columns 40–40,
row 98 columns 41–41, row 98 columns 42–42, row 98 columns 43–43, row 98 columns 44–44, row 98 columns 45–45, row 98
columns 46–46, row 98 columns 47–47, row 98 columns 48–48, row 98 columns 49–49, row 98 columns 50–51), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2667 : rowsJ2 98 99 22 31 ≤ 630047891321 := by decide +kernel

theorem rows22240R_2668 : rowsJ2 98 99 31 35 ≤ 9344009373944 := by decide +kernel

theorem rows22240R_2669 : rowsJ2 98 99 35 37 ≤ 12679511972952 := by decide +kernel

theorem rows22240R_2670 : rowsJ2 98 99 37 38 ≤ 9190051026169 := by decide +kernel

theorem rows22240R_2671 : rowsJ2 98 99 38 39 ≤ 10721168673941 := by decide +kernel

theorem rows22240R_2672 : rowsJ2 98 99 39 40 ≤ 12262330731101 := by decide +kernel

theorem rows22240R_2673 : rowsJ2 98 99 40 41 ≤ 13810692954674 := by decide +kernel

theorem rows22240R_2674 : rowsJ2 98 99 41 42 ≤ 15304657518791 := by decide +kernel

theorem rows22240R_2675 : rowsJ2 98 99 42 43 ≤ 16567336182640 := by decide +kernel

theorem rows22240R_2676 : rowsJ2 98 99 43 44 ≤ 14783997544011 := by decide +kernel

theorem rows22240R_2677 : rowsJ2 98 99 44 45 ≤ 13081698514112 := by decide +kernel

theorem rows22240R_2678 : rowsJ2 98 99 45 46 ≤ 11398972126449 := by decide +kernel

theorem rows22240R_2679 : rowsJ2 98 99 46 47 ≤ 9795319579889 := by decide +kernel

theorem rows22240R_2680 : rowsJ2 98 99 47 48 ≤ 8208612474141 := by decide +kernel

theorem rows22240R_2681 : rowsJ2 98 99 48 49 ≤ 6798341931309 := by decide +kernel

theorem rows22240R_2682 : rowsJ2 98 99 49 50 ≤ 5560963701978 := by decide +kernel

theorem rows22240R_2683 : rowsJ2 98 99 50 52 ≤ 8086026567772 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2667
#print axioms SieveCert.rows22240R_2683
