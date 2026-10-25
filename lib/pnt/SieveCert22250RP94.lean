/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1022–1034 of 4715

File 94 of 351: the parts `rows22250R_1022` … `rows22250R_1034` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 92113 tests: row 63 columns 41–41, row 63 columns 42–42, row 63 columns
43–43, row 63 columns 44–44, row 63 columns 45–45, row 63 columns 46–46, row 63 columns 47–47, row 63 columns 48–48,
row 63 columns 49–49, row 63 columns 50–50, row 63 columns 51–51, row 63 columns 52–52, row 63 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1022 : rowsJ2 63 64 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1023 : rowsJ2 63 64 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1024 : rowsJ2 63 64 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1025 : rowsJ2 63 64 44 45 ≤ 67057654168 := by decide +kernel

theorem rows22250R_1026 : rowsJ2 63 64 45 46 ≤ 263201450003 := by decide +kernel

theorem rows22250R_1027 : rowsJ2 63 64 46 47 ≤ 785221697604 := by decide +kernel

theorem rows22250R_1028 : rowsJ2 63 64 47 48 ≤ 1559328490803 := by decide +kernel

theorem rows22250R_1029 : rowsJ2 63 64 48 49 ≤ 2304141303598 := by decide +kernel

theorem rows22250R_1030 : rowsJ2 63 64 49 50 ≤ 3151596721726 := by decide +kernel

theorem rows22250R_1031 : rowsJ2 63 64 50 51 ≤ 4233756374610 := by decide +kernel

theorem rows22250R_1032 : rowsJ2 63 64 51 52 ≤ 5547173418043 := by decide +kernel

theorem rows22250R_1033 : rowsJ2 63 64 52 53 ≤ 6711290438100 := by decide +kernel

theorem rows22250R_1034 : rowsJ2 63 64 53 54 ≤ 7718554803815 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1022
#print axioms SieveCert.rows22250R_1034
