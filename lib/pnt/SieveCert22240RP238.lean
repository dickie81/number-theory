/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2817–2831 of 5066

File 238 of 387: the parts `rows22240R_2817` … `rows22240R_2831` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95169 in units of a depth-4 test: row 101 columns 49–50, row 101
columns 51–52, row 101 columns 53–55, row 101 columns 56–60, row 101 columns 61–67, row 101 columns 68–72, row 101
columns 73–76, row 101 columns 77–78, row 101 columns 79–79, row 101 columns 80–80, row 101 columns 81–81, row 101
columns 82–82, row 101 columns 83–83, row 101 columns 84–84, row 101 columns 85–85), each a sum of refined costs
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

theorem rows22240R_2817 : rowsJ2 101 102 49 51 ≤ 6432914962137 := by decide +kernel

theorem rows22240R_2818 : rowsJ2 101 102 51 53 ≤ 3599447750263 := by decide +kernel

theorem rows22240R_2819 : rowsJ2 101 102 53 56 ≤ 1684660624483 := by decide +kernel

theorem rows22240R_2820 : rowsJ2 101 102 56 61 ≤ 0 := by decide +kernel

theorem rows22240R_2821 : rowsJ2 101 102 61 68 ≤ 0 := by decide +kernel

theorem rows22240R_2822 : rowsJ2 101 102 68 73 ≤ 0 := by decide +kernel

theorem rows22240R_2823 : rowsJ2 101 102 73 77 ≤ 57564690710 := by decide +kernel

theorem rows22240R_2824 : rowsJ2 101 102 77 79 ≤ 528951871854 := by decide +kernel

theorem rows22240R_2825 : rowsJ2 101 102 79 80 ≤ 598069193202 := by decide +kernel

theorem rows22240R_2826 : rowsJ2 101 102 80 81 ≤ 910416024314 := by decide +kernel

theorem rows22240R_2827 : rowsJ2 101 102 81 82 ≤ 1375944258883 := by decide +kernel

theorem rows22240R_2828 : rowsJ2 101 102 82 83 ≤ 1721606885163 := by decide +kernel

theorem rows22240R_2829 : rowsJ2 101 102 83 84 ≤ 1886233979226 := by decide +kernel

theorem rows22240R_2830 : rowsJ2 101 102 84 85 ≤ 1743658082595 := by decide +kernel

theorem rows22240R_2831 : rowsJ2 101 102 85 86 ≤ 1678049779158 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2817
#print axioms SieveCert.rows22240R_2831
