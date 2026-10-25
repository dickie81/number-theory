/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2884–2897 of 5796

File 262 of 465: the parts `rows22250R_2884` … `rows22250R_2897` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 99028 tests: row 100 columns 97–97, row 100 columns 98–98, row 100 columns
99–99, row 100 columns 100–359, row 101 columns 0–15, row 101 columns 16–20, row 101 columns 21–29, row 101 columns
30–34, row 101 columns 35–36, row 101 columns 37–38, row 101 columns 39–39, row 101 columns 40–40, row 101 columns
41–41, row 101 columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2884 : rowsJ2 100 101 97 98 ≤ 3153905317901 := by decide +kernel

theorem rows22250R_2885 : rowsJ2 100 101 98 99 ≤ 3346365702478 := by decide +kernel

theorem rows22250R_2886 : rowsJ2 100 101 99 100 ≤ 3603258809062 := by decide +kernel

theorem rows22250R_2887 : rowsJ2 100 101 100 360 ≤ 3905384960165 := by decide +kernel

theorem rows22250R_2888 : rowsJ2 101 102 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2889 : rowsJ2 101 102 16 21 ≤ 0 := by decide +kernel

theorem rows22250R_2890 : rowsJ2 101 102 21 30 ≤ 0 := by decide +kernel

theorem rows22250R_2891 : rowsJ2 101 102 30 35 ≤ 3062576163864 := by decide +kernel

theorem rows22250R_2892 : rowsJ2 101 102 35 37 ≤ 6064504070761 := by decide +kernel

theorem rows22250R_2893 : rowsJ2 101 102 37 39 ≤ 11207254475535 := by decide +kernel

theorem rows22250R_2894 : rowsJ2 101 102 39 40 ≤ 7694395277560 := by decide +kernel

theorem rows22250R_2895 : rowsJ2 101 102 40 41 ≤ 8825108014444 := by decide +kernel

theorem rows22250R_2896 : rowsJ2 101 102 41 42 ≤ 10053718571421 := by decide +kernel

theorem rows22250R_2897 : rowsJ2 101 102 42 43 ≤ 11375601531655 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2884
#print axioms SieveCert.rows22250R_2897
