/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2030–2043 of 4715

File 170 of 351: the parts `rows22250R_2030` … `rows22250R_2043` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 92555 in units of a depth-4 test: row 86 columns 45–45, row 86 columns
46–46, row 86 columns 47–47, row 86 columns 48–48, row 86 columns 49–49, row 86 columns 50–50, row 86 columns 51–51,
row 86 columns 52–52, row 86 columns 53–53, row 86 columns 54–54, row 86 columns 55–55, row 86 columns 56–56, row 86
columns 57–57, row 86 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2030 : rowsJ2 86 87 45 46 ≤ 3956727778886 := by decide +kernel

theorem rows22250R_2031 : rowsJ2 86 87 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2032 : rowsJ2 86 87 47 48 ≤ 0 := by decide +kernel

theorem rows22250R_2033 : rowsJ2 86 87 48 49 ≤ 0 := by decide +kernel

theorem rows22250R_2034 : rowsJ2 86 87 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_2035 : rowsJ2 86 87 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2036 : rowsJ2 86 87 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2037 : rowsJ2 86 87 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2038 : rowsJ2 86 87 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2039 : rowsJ2 86 87 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2040 : rowsJ2 86 87 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2041 : rowsJ2 86 87 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2042 : rowsJ2 86 87 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2043 : rowsJ2 86 87 58 59 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2030
#print axioms SieveCert.rows22250R_2043
