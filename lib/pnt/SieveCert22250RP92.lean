/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 996–1005 of 4715

File 92 of 351: the parts `rows22250R_996` … `rows22250R_1005` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, work 98941 in units of a depth-4 test: row 62 columns 58–58, row 62 columns
59–59, row 62 columns 60–60, row 62 columns 61–61, row 62 columns 62–339, row 63 columns 0–17, row 63 columns 18–20,
row 63 columns 21–22, row 63 columns 23–23, row 63 columns 24–24), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_996 : rowsJ2 62 63 58 59 ≤ 12679324848211 := by decide +kernel

theorem rows22250R_997 : rowsJ2 62 63 59 60 ≤ 12879435639854 := by decide +kernel

theorem rows22250R_998 : rowsJ2 62 63 60 61 ≤ 12297208049508 := by decide +kernel

theorem rows22250R_999 : rowsJ2 62 63 61 62 ≤ 11772525562506 := by decide +kernel

theorem rows22250R_1000 : rowsJ2 62 63 62 340 ≤ 11183941352664 := by decide +kernel

theorem rows22250R_1001 : rowsJ2 63 64 0 18 ≤ 1982554402163 := by decide +kernel

theorem rows22250R_1002 : rowsJ2 63 64 18 21 ≤ 88659154276 := by decide +kernel

theorem rows22250R_1003 : rowsJ2 63 64 21 23 ≤ 13952089862 := by decide +kernel

theorem rows22250R_1004 : rowsJ2 63 64 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1005 : rowsJ2 63 64 24 25 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_996
#print axioms SieveCert.rows22250R_1005
