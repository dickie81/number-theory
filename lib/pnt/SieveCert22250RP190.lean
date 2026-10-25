/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1970–1983 of 5796

File 190 of 465: the parts `rows22250R_1970` … `rows22250R_1983` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 92668 tests: row 82 columns 27–28, row 82 columns 29–30, row 82 columns
31–32, row 82 columns 33–35, row 82 columns 36–38, row 82 columns 39–40, row 82 columns 41–42, row 82 columns 43–43,
row 82 columns 44–44, row 82 columns 45–45, row 82 columns 46–46, row 82 columns 47–47, row 82 columns 48–48, row 82
columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1970 : rowsJ2 82 83 27 29 ≤ 0 := by decide +kernel

theorem rows22250R_1971 : rowsJ2 82 83 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_1972 : rowsJ2 82 83 31 33 ≤ 0 := by decide +kernel

theorem rows22250R_1973 : rowsJ2 82 83 33 36 ≤ 0 := by decide +kernel

theorem rows22250R_1974 : rowsJ2 82 83 36 39 ≤ 0 := by decide +kernel

theorem rows22250R_1975 : rowsJ2 82 83 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1976 : rowsJ2 82 83 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1977 : rowsJ2 82 83 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1978 : rowsJ2 82 83 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1979 : rowsJ2 82 83 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1980 : rowsJ2 82 83 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1981 : rowsJ2 82 83 47 48 ≤ 93700914827 := by decide +kernel

theorem rows22250R_1982 : rowsJ2 82 83 48 49 ≤ 419952409651 := by decide +kernel

theorem rows22250R_1983 : rowsJ2 82 83 49 50 ≤ 782006247957 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1970
#print axioms SieveCert.rows22250R_1983
