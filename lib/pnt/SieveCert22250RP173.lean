/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2071–2085 of 4715

File 173 of 351: the parts `rows22250R_2071` … `rows22250R_2085` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98683 tests: row 87 columns 45–45, row 87 columns 46–46, row 87 columns
47–47, row 87 columns 48–48, row 87 columns 49–49, row 87 columns 50–50, row 87 columns 51–51, row 87 columns 52–52,
row 87 columns 53–53, row 87 columns 54–54, row 87 columns 55–55, row 87 columns 56–56, row 87 columns 57–57, row 87
columns 58–59, row 87 columns 60–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2071 : rowsJ2 87 88 45 46 ≤ 8292998195583 := by decide +kernel

theorem rows22250R_2072 : rowsJ2 87 88 46 47 ≤ 4713511032803 := by decide +kernel

theorem rows22250R_2073 : rowsJ2 87 88 47 48 ≤ 0 := by decide +kernel

theorem rows22250R_2074 : rowsJ2 87 88 48 49 ≤ 0 := by decide +kernel

theorem rows22250R_2075 : rowsJ2 87 88 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_2076 : rowsJ2 87 88 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2077 : rowsJ2 87 88 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2078 : rowsJ2 87 88 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2079 : rowsJ2 87 88 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2080 : rowsJ2 87 88 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2081 : rowsJ2 87 88 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2082 : rowsJ2 87 88 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2083 : rowsJ2 87 88 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2084 : rowsJ2 87 88 58 60 ≤ 0 := by decide +kernel

theorem rows22250R_2085 : rowsJ2 87 88 60 62 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2071
#print axioms SieveCert.rows22250R_2085
