/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1111–1125 of 5796

File 116 of 465: the parts `rows22250R_1111` … `rows22250R_1125` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94740 tests: row 65 columns 35–35, row 65 columns 36–36, row 65 columns
37–37, row 65 columns 38–38, row 65 columns 39–39, row 65 columns 40–40, row 65 columns 41–41, row 65 columns 42–42,
row 65 columns 43–43, row 65 columns 44–44, row 65 columns 45–45, row 65 columns 46–46, row 65 columns 47–47, row 65
columns 48–48, row 65 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1111 : rowsJ2 65 66 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1112 : rowsJ2 65 66 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1113 : rowsJ2 65 66 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1114 : rowsJ2 65 66 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1115 : rowsJ2 65 66 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1116 : rowsJ2 65 66 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1117 : rowsJ2 65 66 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1118 : rowsJ2 65 66 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1119 : rowsJ2 65 66 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1120 : rowsJ2 65 66 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1121 : rowsJ2 65 66 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1122 : rowsJ2 65 66 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1123 : rowsJ2 65 66 47 48 ≤ 107576637736 := by decide +kernel

theorem rows22250R_1124 : rowsJ2 65 66 48 49 ≤ 482141165037 := by decide +kernel

theorem rows22250R_1125 : rowsJ2 65 66 49 50 ≤ 897809834613 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1111
#print axioms SieveCert.rows22250R_1125
