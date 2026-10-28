/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 913–926 of 5066

File 91 of 387: the parts `rows22240R_913` … `rows22240R_926` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98054 in units of a depth-4 test: row 60 columns 34–34, row 60 columns
35–35, row 60 columns 36–36, row 60 columns 37–37, row 60 columns 38–38, row 60 columns 39–39, row 60 columns 40–40,
row 60 columns 41–41, row 60 columns 42–42, row 60 columns 43–43, row 60 columns 44–44, row 60 columns 45–45, row 60
columns 46–46, row 60 columns 47–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_913 : rowsJ2 60 61 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_914 : rowsJ2 60 61 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_915 : rowsJ2 60 61 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_916 : rowsJ2 60 61 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_917 : rowsJ2 60 61 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_918 : rowsJ2 60 61 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_919 : rowsJ2 60 61 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_920 : rowsJ2 60 61 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_921 : rowsJ2 60 61 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_922 : rowsJ2 60 61 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_923 : rowsJ2 60 61 44 45 ≤ 69963085262 := by decide +kernel

theorem rows22240R_924 : rowsJ2 60 61 45 46 ≤ 204602993003 := by decide +kernel

theorem rows22240R_925 : rowsJ2 60 61 46 47 ≤ 399004508522 := by decide +kernel

theorem rows22240R_926 : rowsJ2 60 61 47 48 ≤ 851907813846 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_913
#print axioms SieveCert.rows22240R_926
