/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1033–1045 of 5066

File 102 of 387: the parts `rows22240R_1033` … `rows22240R_1045` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 94847 in units of a depth-4 test: row 63 columns 28–28, row 63 columns
29–29, row 63 columns 30–30, row 63 columns 31–31, row 63 columns 32–32, row 63 columns 33–33, row 63 columns 34–34,
row 63 columns 35–35, row 63 columns 36–36, row 63 columns 37–37, row 63 columns 38–38, row 63 columns 39–39, row 63
columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_1033 : rowsJ2 63 64 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1034 : rowsJ2 63 64 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1035 : rowsJ2 63 64 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1036 : rowsJ2 63 64 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1037 : rowsJ2 63 64 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1038 : rowsJ2 63 64 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1039 : rowsJ2 63 64 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1040 : rowsJ2 63 64 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1041 : rowsJ2 63 64 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1042 : rowsJ2 63 64 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1043 : rowsJ2 63 64 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1044 : rowsJ2 63 64 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_1045 : rowsJ2 63 64 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1033
#print axioms SieveCert.rows22240R_1045
