/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1006–1021 of 4715

File 93 of 351: the parts `rows22250R_1006` … `rows22250R_1021` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 95906 in units of a depth-4 test: row 63 columns 25–25, row 63 columns
26–26, row 63 columns 27–27, row 63 columns 28–28, row 63 columns 29–29, row 63 columns 30–30, row 63 columns 31–31,
row 63 columns 32–32, row 63 columns 33–33, row 63 columns 34–34, row 63 columns 35–35, row 63 columns 36–36, row 63
columns 37–37, row 63 columns 38–38, row 63 columns 39–39, row 63 columns 40–40), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1006 : rowsJ2 63 64 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1007 : rowsJ2 63 64 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1008 : rowsJ2 63 64 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1009 : rowsJ2 63 64 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1010 : rowsJ2 63 64 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1011 : rowsJ2 63 64 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1012 : rowsJ2 63 64 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1013 : rowsJ2 63 64 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1014 : rowsJ2 63 64 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1015 : rowsJ2 63 64 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1016 : rowsJ2 63 64 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1017 : rowsJ2 63 64 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1018 : rowsJ2 63 64 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1019 : rowsJ2 63 64 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1020 : rowsJ2 63 64 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1021 : rowsJ2 63 64 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1006
#print axioms SieveCert.rows22250R_1021
