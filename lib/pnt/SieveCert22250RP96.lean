/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1042–1053 of 4715

File 96 of 351: the parts `rows22250R_1042` … `rows22250R_1053` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 95722 in units of a depth-4 test: row 63 columns 61–61, row 63 columns
62–62, row 63 columns 63–339, row 64 columns 0–17, row 64 columns 18–20, row 64 columns 21–22, row 64 columns 23–23,
row 64 columns 24–24, row 64 columns 25–25, row 64 columns 26–26, row 64 columns 27–27, row 64 columns 28–28), each
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

theorem rows22250R_1042 : rowsJ2 63 64 61 62 ≤ 10468105291946 := by decide +kernel

theorem rows22250R_1043 : rowsJ2 63 64 62 63 ≤ 9935326767246 := by decide +kernel

theorem rows22250R_1044 : rowsJ2 63 64 63 340 ≤ 9408350808570 := by decide +kernel

theorem rows22250R_1045 : rowsJ2 64 65 0 18 ≤ 1795860206831 := by decide +kernel

theorem rows22250R_1046 : rowsJ2 64 65 18 21 ≤ 56276202641 := by decide +kernel

theorem rows22250R_1047 : rowsJ2 64 65 21 23 ≤ 4663695117 := by decide +kernel

theorem rows22250R_1048 : rowsJ2 64 65 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1049 : rowsJ2 64 65 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1050 : rowsJ2 64 65 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1051 : rowsJ2 64 65 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1052 : rowsJ2 64 65 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1053 : rowsJ2 64 65 28 29 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1042
#print axioms SieveCert.rows22250R_1053
