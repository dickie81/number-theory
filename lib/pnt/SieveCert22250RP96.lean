/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 904–916 of 5796

File 96 of 465: the parts `rows22250R_904` … `rows22250R_916` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 98374 tests: row 60 columns 38–38, row 60 columns 39–39, row 60 columns
40–40, row 60 columns 41–41, row 60 columns 42–42, row 60 columns 43–43, row 60 columns 44–44, row 60 columns 45–45,
row 60 columns 46–46, row 60 columns 47–47, row 60 columns 48–48, row 60 columns 49–49, row 60 columns 50–50), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_904 : rowsJ2 60 61 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_905 : rowsJ2 60 61 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_906 : rowsJ2 60 61 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_907 : rowsJ2 60 61 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_908 : rowsJ2 60 61 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_909 : rowsJ2 60 61 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_910 : rowsJ2 60 61 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_911 : rowsJ2 60 61 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_912 : rowsJ2 60 61 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_913 : rowsJ2 60 61 47 48 ≤ 112475447800 := by decide +kernel

theorem rows22250R_914 : rowsJ2 60 61 48 49 ≤ 504096842790 := by decide +kernel

theorem rows22250R_915 : rowsJ2 60 61 49 50 ≤ 938694174808 := by decide +kernel

theorem rows22250R_916 : rowsJ2 60 61 50 51 ≤ 1411823787673 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_904
#print axioms SieveCert.rows22250R_916
