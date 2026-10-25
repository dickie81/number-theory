/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 957–969 of 4715

File 89 of 351: the parts `rows22250R_957` … `rows22250R_969` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96163 tests: row 61 columns 61–339, row 62 columns 0–17, row 62 columns
18–20, row 62 columns 21–22, row 62 columns 23–23, row 62 columns 24–24, row 62 columns 25–25, row 62 columns 26–26,
row 62 columns 27–27, row 62 columns 28–28, row 62 columns 29–29, row 62 columns 30–30, row 62 columns 31–31), each
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

theorem rows22250R_957 : rowsJ2 61 62 61 340 ≤ 13089132916161 := by decide +kernel

theorem rows22250R_958 : rowsJ2 62 63 0 18 ≤ 2171035814117 := by decide +kernel

theorem rows22250R_959 : rowsJ2 62 63 18 21 ≤ 125500532728 := by decide +kernel

theorem rows22250R_960 : rowsJ2 62 63 21 23 ≤ 27772124572 := by decide +kernel

theorem rows22250R_961 : rowsJ2 62 63 23 24 ≤ 4613611924 := by decide +kernel

theorem rows22250R_962 : rowsJ2 62 63 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_963 : rowsJ2 62 63 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_964 : rowsJ2 62 63 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_965 : rowsJ2 62 63 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_966 : rowsJ2 62 63 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_967 : rowsJ2 62 63 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_968 : rowsJ2 62 63 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_969 : rowsJ2 62 63 31 32 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_957
#print axioms SieveCert.rows22250R_969
