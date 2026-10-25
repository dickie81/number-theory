/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2898–2912 of 5796

File 263 of 465: the parts `rows22250R_2898` … `rows22250R_2912` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95071 tests: row 101 columns 43–43, row 101 columns 44–44, row 101 columns
45–45, row 101 columns 46–46, row 101 columns 47–47, row 101 columns 48–48, row 101 columns 49–49, row 101 columns
50–50, row 101 columns 51–51, row 101 columns 52–52, row 101 columns 53–53, row 101 columns 54–54, row 101 columns
55–56, row 101 columns 57–58, row 101 columns 59–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2898 : rowsJ2 101 102 43 44 ≤ 12786510062972 := by decide +kernel

theorem rows22250R_2899 : rowsJ2 101 102 44 45 ≤ 14008756625543 := by decide +kernel

theorem rows22250R_2900 : rowsJ2 101 102 45 46 ≤ 13764462149480 := by decide +kernel

theorem rows22250R_2901 : rowsJ2 101 102 46 47 ≤ 12195583054466 := by decide +kernel

theorem rows22250R_2902 : rowsJ2 101 102 47 48 ≤ 10691937161507 := by decide +kernel

theorem rows22250R_2903 : rowsJ2 101 102 48 49 ≤ 9285522057796 := by decide +kernel

theorem rows22250R_2904 : rowsJ2 101 102 49 50 ≤ 8021191188236 := by decide +kernel

theorem rows22250R_2905 : rowsJ2 101 102 50 51 ≤ 6846304958247 := by decide +kernel

theorem rows22250R_2906 : rowsJ2 101 102 51 52 ≤ 5806818432141 := by decide +kernel

theorem rows22250R_2907 : rowsJ2 101 102 52 53 ≤ 4827278236374 := by decide +kernel

theorem rows22250R_2908 : rowsJ2 101 102 53 54 ≤ 3907995206926 := by decide +kernel

theorem rows22250R_2909 : rowsJ2 101 102 54 55 ≤ 3049379890805 := by decide +kernel

theorem rows22250R_2910 : rowsJ2 101 102 55 57 ≤ 2598236298573 := by decide +kernel

theorem rows22250R_2911 : rowsJ2 101 102 57 59 ≤ 266777571065 := by decide +kernel

theorem rows22250R_2912 : rowsJ2 101 102 59 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2898
#print axioms SieveCert.rows22250R_2912
