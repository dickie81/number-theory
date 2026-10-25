/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1017–1026 of 5796

File 107 of 465: the parts `rows22250R_1017` … `rows22250R_1026` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 95242 tests: row 63 columns 28–28, row 63 columns 29–29, row 63 columns
30–30, row 63 columns 31–31, row 63 columns 32–32, row 63 columns 33–33, row 63 columns 34–34, row 63 columns 35–35,
row 63 columns 36–36, row 63 columns 37–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1017 : rowsJ2 63 64 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1018 : rowsJ2 63 64 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1019 : rowsJ2 63 64 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1020 : rowsJ2 63 64 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1021 : rowsJ2 63 64 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1022 : rowsJ2 63 64 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1023 : rowsJ2 63 64 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1024 : rowsJ2 63 64 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1025 : rowsJ2 63 64 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1026 : rowsJ2 63 64 37 38 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1017
#print axioms SieveCert.rows22250R_1026
