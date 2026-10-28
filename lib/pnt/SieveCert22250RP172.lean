/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2058–2070 of 4715

File 172 of 351: the parts `rows22250R_2058` … `rows22250R_2070` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 95160 in units of a depth-4 test: row 86 columns 86–339, row 87 columns
0–16, row 87 columns 17–19, row 87 columns 20–23, row 87 columns 24–28, row 87 columns 29–34, row 87 columns 35–37,
row 87 columns 38–39, row 87 columns 40–40, row 87 columns 41–41, row 87 columns 42–42, row 87 columns 43–43, row 87
columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2058 : rowsJ2 86 87 86 340 ≤ 6261566861417 := by decide +kernel

theorem rows22250R_2059 : rowsJ2 87 88 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2060 : rowsJ2 87 88 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2061 : rowsJ2 87 88 20 24 ≤ 0 := by decide +kernel

theorem rows22250R_2062 : rowsJ2 87 88 24 29 ≤ 0 := by decide +kernel

theorem rows22250R_2063 : rowsJ2 87 88 29 35 ≤ 2913272939238 := by decide +kernel

theorem rows22250R_2064 : rowsJ2 87 88 35 38 ≤ 12198268292359 := by decide +kernel

theorem rows22250R_2065 : rowsJ2 87 88 38 40 ≤ 14591388092279 := by decide +kernel

theorem rows22250R_2066 : rowsJ2 87 88 40 41 ≤ 9209559360027 := by decide +kernel

theorem rows22250R_2067 : rowsJ2 87 88 41 42 ≤ 10511063031434 := by decide +kernel

theorem rows22250R_2068 : rowsJ2 87 88 42 43 ≤ 11827879930623 := by decide +kernel

theorem rows22250R_2069 : rowsJ2 87 88 43 44 ≤ 13252314270188 := by decide +kernel

theorem rows22250R_2070 : rowsJ2 87 88 44 45 ≤ 11396290488015 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2058
#print axioms SieveCert.rows22250R_2070
