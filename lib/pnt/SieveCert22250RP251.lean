/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2748–2762 of 5796

File 251 of 465: the parts `rows22250R_2748` … `rows22250R_2762` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99172 tests: row 98 columns 39–39, row 98 columns 40–40, row 98 columns
41–41, row 98 columns 42–42, row 98 columns 43–43, row 98 columns 44–44, row 98 columns 45–45, row 98 columns 46–46,
row 98 columns 47–47, row 98 columns 48–48, row 98 columns 49–49, row 98 columns 50–50, row 98 columns 51–51, row 98
columns 52–52, row 98 columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2748 : rowsJ2 98 99 39 40 ≤ 6651194704387 := by decide +kernel

theorem rows22250R_2749 : rowsJ2 98 99 40 41 ≤ 7733274942031 := by decide +kernel

theorem rows22250R_2750 : rowsJ2 98 99 41 42 ≤ 8832332466919 := by decide +kernel

theorem rows22250R_2751 : rowsJ2 98 99 42 43 ≤ 9945800873426 := by decide +kernel

theorem rows22250R_2752 : rowsJ2 98 99 43 44 ≤ 11150861101233 := by decide +kernel

theorem rows22250R_2753 : rowsJ2 98 99 44 45 ≤ 12443312954769 := by decide +kernel

theorem rows22250R_2754 : rowsJ2 98 99 45 46 ≤ 13635137817168 := by decide +kernel

theorem rows22250R_2755 : rowsJ2 98 99 46 47 ≤ 14725783589240 := by decide +kernel

theorem rows22250R_2756 : rowsJ2 98 99 47 48 ≤ 13117703101402 := by decide +kernel

theorem rows22250R_2757 : rowsJ2 98 99 48 49 ≤ 11654591223728 := by decide +kernel

theorem rows22250R_2758 : rowsJ2 98 99 49 50 ≤ 10285200816665 := by decide +kernel

theorem rows22250R_2759 : rowsJ2 98 99 50 51 ≤ 9053454784617 := by decide +kernel

theorem rows22250R_2760 : rowsJ2 98 99 51 52 ≤ 7907991414555 := by decide +kernel

theorem rows22250R_2761 : rowsJ2 98 99 52 53 ≤ 5367595393528 := by decide +kernel

theorem rows22250R_2762 : rowsJ2 98 99 53 54 ≤ 3091800667574 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2748
#print axioms SieveCert.rows22250R_2762
