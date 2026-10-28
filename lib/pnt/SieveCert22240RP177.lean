/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1989–2001 of 5066

File 177 of 387: the parts `rows22240R_1989` … `rows22240R_2001` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 90945 in units of a depth-4 test: row 83 columns 26–28, row 83 columns
29–31, row 83 columns 32–35, row 83 columns 36–38, row 83 columns 39–40, row 83 columns 41–41, row 83 columns 42–42,
row 83 columns 43–43, row 83 columns 44–44, row 83 columns 45–45, row 83 columns 46–46, row 83 columns 47–47, row 83
columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1989 : rowsJ2 83 84 26 29 ≤ 0 := by decide +kernel

theorem rows22240R_1990 : rowsJ2 83 84 29 32 ≤ 0 := by decide +kernel

theorem rows22240R_1991 : rowsJ2 83 84 32 36 ≤ 1701451551877 := by decide +kernel

theorem rows22240R_1992 : rowsJ2 83 84 36 39 ≤ 8166354537674 := by decide +kernel

theorem rows22240R_1993 : rowsJ2 83 84 39 41 ≤ 10324692316109 := by decide +kernel

theorem rows22240R_1994 : rowsJ2 83 84 41 42 ≤ 5045840907218 := by decide +kernel

theorem rows22240R_1995 : rowsJ2 83 84 42 43 ≤ 4144592053803 := by decide +kernel

theorem rows22240R_1996 : rowsJ2 83 84 43 44 ≤ 2405697423448 := by decide +kernel

theorem rows22240R_1997 : rowsJ2 83 84 44 45 ≤ 57550624510 := by decide +kernel

theorem rows22240R_1998 : rowsJ2 83 84 45 46 ≤ 168303470035 := by decide +kernel

theorem rows22240R_1999 : rowsJ2 83 84 46 47 ≤ 275475913325 := by decide +kernel

theorem rows22240R_2000 : rowsJ2 83 84 47 48 ≤ 386454520019 := by decide +kernel

theorem rows22240R_2001 : rowsJ2 83 84 48 49 ≤ 503996191816 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1989
#print axioms SieveCert.rows22240R_2001
