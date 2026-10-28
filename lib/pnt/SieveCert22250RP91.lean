/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 987–995 of 4715

File 91 of 351: the parts `rows22250R_987` … `rows22250R_995` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 99109 in units of a depth-4 test: row 62 columns 49–49, row 62 columns
50–50, row 62 columns 51–51, row 62 columns 52–52, row 62 columns 53–53, row 62 columns 54–54, row 62 columns 55–55,
row 62 columns 56–56, row 62 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_987 : rowsJ2 62 63 49 50 ≤ 3180501928352 := by decide +kernel

theorem rows22250R_988 : rowsJ2 62 63 50 51 ≤ 4272586724310 := by decide +kernel

theorem rows22250R_989 : rowsJ2 62 63 51 52 ≤ 5598049912731 := by decide +kernel

theorem rows22250R_990 : rowsJ2 62 63 52 53 ≤ 6822150135024 := by decide +kernel

theorem rows22250R_991 : rowsJ2 62 63 53 54 ≤ 7938841893217 := by decide +kernel

theorem rows22250R_992 : rowsJ2 62 63 54 55 ≤ 9037958201636 := by decide +kernel

theorem rows22250R_993 : rowsJ2 62 63 55 56 ≤ 10169737615984 := by decide +kernel

theorem rows22250R_994 : rowsJ2 62 63 56 57 ≤ 11066864929473 := by decide +kernel

theorem rows22250R_995 : rowsJ2 62 63 57 58 ≤ 11849065536758 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_987
#print axioms SieveCert.rows22250R_995
