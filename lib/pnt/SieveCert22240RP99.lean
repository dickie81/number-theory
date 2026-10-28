/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1002–1014 of 5066

File 99 of 387: the parts `rows22240R_1002` … `rows22240R_1014` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 90663 in units of a depth-4 test: row 62 columns 40–40, row 62 columns
41–41, row 62 columns 42–42, row 62 columns 43–43, row 62 columns 44–44, row 62 columns 45–45, row 62 columns 46–46,
row 62 columns 47–47, row 62 columns 48–48, row 62 columns 49–49, row 62 columns 50–50, row 62 columns 51–51, row 62
columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_1002 : rowsJ2 62 63 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1003 : rowsJ2 62 63 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1004 : rowsJ2 62 63 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1005 : rowsJ2 62 63 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1006 : rowsJ2 62 63 44 45 ≤ 68675100197 := by decide +kernel

theorem rows22240R_1007 : rowsJ2 62 63 45 46 ≤ 200836355239 := by decide +kernel

theorem rows22240R_1008 : rowsJ2 62 63 46 47 ≤ 391659037042 := by decide +kernel

theorem rows22240R_1009 : rowsJ2 62 63 47 48 ≤ 836224621261 := by decide +kernel

theorem rows22240R_1010 : rowsJ2 62 63 48 49 ≤ 1597606933613 := by decide +kernel

theorem rows22240R_1011 : rowsJ2 62 63 49 50 ≤ 2463719563489 := by decide +kernel

theorem rows22240R_1012 : rowsJ2 62 63 50 51 ≤ 3361726763857 := by decide +kernel

theorem rows22240R_1013 : rowsJ2 62 63 51 52 ≤ 4423190349914 := by decide +kernel

theorem rows22240R_1014 : rowsJ2 62 63 52 53 ≤ 5781304704930 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1002
#print axioms SieveCert.rows22240R_1014
