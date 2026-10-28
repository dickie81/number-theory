/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 990–1001 of 5066

File 98 of 387: the parts `rows22240R_990` … `rows22240R_1001` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 94604 in units of a depth-4 test: row 62 columns 28–28, row 62 columns
29–29, row 62 columns 30–30, row 62 columns 31–31, row 62 columns 32–32, row 62 columns 33–33, row 62 columns 34–34,
row 62 columns 35–35, row 62 columns 36–36, row 62 columns 37–37, row 62 columns 38–38, row 62 columns 39–39), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_990 : rowsJ2 62 63 28 29 ≤ 4108041304 := by decide +kernel

theorem rows22240R_991 : rowsJ2 62 63 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_992 : rowsJ2 62 63 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_993 : rowsJ2 62 63 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_994 : rowsJ2 62 63 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_995 : rowsJ2 62 63 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_996 : rowsJ2 62 63 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_997 : rowsJ2 62 63 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_998 : rowsJ2 62 63 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_999 : rowsJ2 62 63 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1000 : rowsJ2 62 63 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1001 : rowsJ2 62 63 39 40 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_990
#print axioms SieveCert.rows22240R_1001
