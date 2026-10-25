/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1988–2001 of 4715

File 167 of 351: the parts `rows22250R_1988` … `rows22250R_2001` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96921 tests: row 85 columns 45–45, row 85 columns 46–46, row 85 columns
47–47, row 85 columns 48–48, row 85 columns 49–49, row 85 columns 50–50, row 85 columns 51–51, row 85 columns 52–52,
row 85 columns 53–53, row 85 columns 54–54, row 85 columns 55–55, row 85 columns 56–56, row 85 columns 57–57, row 85
columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1988 : rowsJ2 85 86 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1989 : rowsJ2 85 86 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1990 : rowsJ2 85 86 47 48 ≤ 0 := by decide +kernel

theorem rows22250R_1991 : rowsJ2 85 86 48 49 ≤ 0 := by decide +kernel

theorem rows22250R_1992 : rowsJ2 85 86 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_1993 : rowsJ2 85 86 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_1994 : rowsJ2 85 86 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_1995 : rowsJ2 85 86 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_1996 : rowsJ2 85 86 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_1997 : rowsJ2 85 86 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_1998 : rowsJ2 85 86 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_1999 : rowsJ2 85 86 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2000 : rowsJ2 85 86 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2001 : rowsJ2 85 86 58 59 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1988
#print axioms SieveCert.rows22250R_2001
