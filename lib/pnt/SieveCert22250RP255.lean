/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2796–2810 of 5796

File 255 of 465: the parts `rows22250R_2796` … `rows22250R_2810` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97975 tests: row 99 columns 37–38, row 99 columns 39–39, row 99 columns
40–40, row 99 columns 41–41, row 99 columns 42–42, row 99 columns 43–43, row 99 columns 44–44, row 99 columns 45–45,
row 99 columns 46–46, row 99 columns 47–47, row 99 columns 48–48, row 99 columns 49–49, row 99 columns 50–50, row 99
columns 51–51, row 99 columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2796 : rowsJ2 99 100 37 39 ≤ 9646390863088 := by decide +kernel

theorem rows22250R_2797 : rowsJ2 99 100 39 40 ≤ 7027597973976 := by decide +kernel

theorem rows22250R_2798 : rowsJ2 99 100 40 41 ≤ 8097716702135 := by decide +kernel

theorem rows22250R_2799 : rowsJ2 99 100 41 42 ≤ 9184801914180 := by decide +kernel

theorem rows22250R_2800 : rowsJ2 99 100 42 43 ≤ 10367033902934 := by decide +kernel

theorem rows22250R_2801 : rowsJ2 99 100 43 44 ≤ 11639954283420 := by decide +kernel

theorem rows22250R_2802 : rowsJ2 99 100 44 45 ≤ 12952885992915 := by decide +kernel

theorem rows22250R_2803 : rowsJ2 99 100 45 46 ≤ 14164187148347 := by decide +kernel

theorem rows22250R_2804 : rowsJ2 99 100 46 47 ≤ 13873466845542 := by decide +kernel

theorem rows22250R_2805 : rowsJ2 99 100 47 48 ≤ 12315806167152 := by decide +kernel

theorem rows22250R_2806 : rowsJ2 99 100 48 49 ≤ 10855735505158 := by decide +kernel

theorem rows22250R_2807 : rowsJ2 99 100 49 50 ≤ 9537123746620 := by decide +kernel

theorem rows22250R_2808 : rowsJ2 99 100 50 51 ≤ 8308240568152 := by decide +kernel

theorem rows22250R_2809 : rowsJ2 99 100 51 52 ≤ 7214026282715 := by decide +kernel

theorem rows22250R_2810 : rowsJ2 99 100 52 53 ≤ 6130152969054 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2796
#print axioms SieveCert.rows22250R_2810
