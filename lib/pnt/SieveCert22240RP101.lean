/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1022–1032 of 5066

File 101 of 387: the parts `rows22240R_1022` … `rows22240R_1032` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 96837 in units of a depth-4 test: row 62 columns 60–60, row 62 columns
61–61, row 62 columns 62–339, row 63 columns 0–16, row 63 columns 17–20, row 63 columns 21–22, row 63 columns 23–23,
row 63 columns 24–24, row 63 columns 25–25, row 63 columns 26–26, row 63 columns 27–27), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1022 : rowsJ2 62 63 60 61 ≤ 13780814799060 := by decide +kernel

theorem rows22240R_1023 : rowsJ2 62 63 61 62 ≤ 13215464225374 := by decide +kernel

theorem rows22240R_1024 : rowsJ2 62 63 62 340 ≤ 12706287254612 := by decide +kernel

theorem rows22240R_1025 : rowsJ2 63 64 0 17 ≤ 2546074289214 := by decide +kernel

theorem rows22240R_1026 : rowsJ2 63 64 17 21 ≤ 463426899998 := by decide +kernel

theorem rows22240R_1027 : rowsJ2 63 64 21 23 ≤ 116130808959 := by decide +kernel

theorem rows22240R_1028 : rowsJ2 63 64 23 24 ≤ 37236500320 := by decide +kernel

theorem rows22240R_1029 : rowsJ2 63 64 24 25 ≤ 24837176667 := by decide +kernel

theorem rows22240R_1030 : rowsJ2 63 64 25 26 ≤ 16524511948 := by decide +kernel

theorem rows22240R_1031 : rowsJ2 63 64 26 27 ≤ 8277495027 := by decide +kernel

theorem rows22240R_1032 : rowsJ2 63 64 27 28 ≤ 4125851268 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1022
#print axioms SieveCert.rows22240R_1032
