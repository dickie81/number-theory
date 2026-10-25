/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1027–1040 of 5796

File 108 of 465: the parts `rows22250R_1027` … `rows22250R_1040` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94228 tests: row 63 columns 38–38, row 63 columns 39–39, row 63 columns
40–40, row 63 columns 41–41, row 63 columns 42–42, row 63 columns 43–43, row 63 columns 44–44, row 63 columns 45–45,
row 63 columns 46–46, row 63 columns 47–47, row 63 columns 48–48, row 63 columns 49–49, row 63 columns 50–50, row 63
columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1027 : rowsJ2 63 64 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1028 : rowsJ2 63 64 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1029 : rowsJ2 63 64 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1030 : rowsJ2 63 64 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1031 : rowsJ2 63 64 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1032 : rowsJ2 63 64 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1033 : rowsJ2 63 64 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1034 : rowsJ2 63 64 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1035 : rowsJ2 63 64 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1036 : rowsJ2 63 64 47 48 ≤ 109484046181 := by decide +kernel

theorem rows22250R_1037 : rowsJ2 63 64 48 49 ≤ 490689862497 := by decide +kernel

theorem rows22250R_1038 : rowsJ2 63 64 49 50 ≤ 913728626058 := by decide +kernel

theorem rows22250R_1039 : rowsJ2 63 64 50 51 ≤ 1374274864345 := by decide +kernel

theorem rows22250R_1040 : rowsJ2 63 64 51 52 ≤ 1978264142582 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1027
#print axioms SieveCert.rows22250R_1040
