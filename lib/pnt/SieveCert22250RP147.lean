/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1701–1712 of 4715

File 147 of 351: the parts `rows22250R_1701` … `rows22250R_1712` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99370 tests: row 78 columns 50–50, row 78 columns 51–51, row 78 columns
52–52, row 78 columns 53–53, row 78 columns 54–54, row 78 columns 55–55, row 78 columns 56–56, row 78 columns 57–57,
row 78 columns 58–58, row 78 columns 59–59, row 78 columns 60–60, row 78 columns 61–61), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1701 : rowsJ2 78 79 50 51 ≤ 1862908556236 := by decide +kernel

theorem rows22250R_1702 : rowsJ2 78 79 51 52 ≤ 1873106964609 := by decide +kernel

theorem rows22250R_1703 : rowsJ2 78 79 52 53 ≤ 1643577837135 := by decide +kernel

theorem rows22250R_1704 : rowsJ2 78 79 53 54 ≤ 1470767984151 := by decide +kernel

theorem rows22250R_1705 : rowsJ2 78 79 54 55 ≤ 1238237051898 := by decide +kernel

theorem rows22250R_1706 : rowsJ2 78 79 55 56 ≤ 1062976857193 := by decide +kernel

theorem rows22250R_1707 : rowsJ2 78 79 56 57 ≤ 889387091017 := by decide +kernel

theorem rows22250R_1708 : rowsJ2 78 79 57 58 ≤ 773206665184 := by decide +kernel

theorem rows22250R_1709 : rowsJ2 78 79 58 59 ≤ 658100364752 := by decide +kernel

theorem rows22250R_1710 : rowsJ2 78 79 59 60 ≤ 600679911042 := by decide +kernel

theorem rows22250R_1711 : rowsJ2 78 79 60 61 ≤ 483659331628 := by decide +kernel

theorem rows22250R_1712 : rowsJ2 78 79 61 62 ≤ 425141308331 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1701
#print axioms SieveCert.rows22250R_1712
