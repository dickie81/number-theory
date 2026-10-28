/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1106–1119 of 4715

File 101 of 351: the parts `rows22250R_1106` … `rows22250R_1119` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 90746 in units of a depth-4 test: row 65 columns 36–36, row 65 columns
37–38, row 65 columns 39–40, row 65 columns 41–41, row 65 columns 42–42, row 65 columns 43–43, row 65 columns 44–44,
row 65 columns 45–45, row 65 columns 46–46, row 65 columns 47–47, row 65 columns 48–48, row 65 columns 49–49, row 65
columns 50–50, row 65 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1106 : rowsJ2 65 66 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1107 : rowsJ2 65 66 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1108 : rowsJ2 65 66 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1109 : rowsJ2 65 66 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1110 : rowsJ2 65 66 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1111 : rowsJ2 65 66 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1112 : rowsJ2 65 66 44 45 ≤ 65860539655 := by decide +kernel

theorem rows22250R_1113 : rowsJ2 65 66 45 46 ≤ 258502772731 := by decide +kernel

theorem rows22250R_1114 : rowsJ2 65 66 46 47 ≤ 771203904984 := by decide +kernel

theorem rows22250R_1115 : rowsJ2 65 66 47 48 ≤ 1531491329047 := by decide +kernel

theorem rows22250R_1116 : rowsJ2 65 66 48 49 ≤ 2263007729398 := by decide +kernel

theorem rows22250R_1117 : rowsJ2 65 66 49 50 ≤ 3095334357352 := by decide +kernel

theorem rows22250R_1118 : rowsJ2 65 66 50 51 ≤ 4158175275618 := by decide +kernel

theorem rows22250R_1119 : rowsJ2 65 66 51 52 ≤ 5399175143112 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1106
#print axioms SieveCert.rows22250R_1119
