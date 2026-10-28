/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1186–1195 of 5066

File 115 of 387: the parts `rows22240R_1186` … `rows22240R_1195` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93920 in units of a depth-4 test: row 66 columns 46–46, row 66 columns
47–47, row 66 columns 48–48, row 66 columns 49–49, row 66 columns 50–50, row 66 columns 51–51, row 66 columns 52–52,
row 66 columns 53–53, row 66 columns 54–54, row 66 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1186 : rowsJ2 66 67 46 47 ≤ 377750655467 := by decide +kernel

theorem rows22240R_1187 : rowsJ2 66 67 47 48 ≤ 806529069737 := by decide +kernel

theorem rows22240R_1188 : rowsJ2 66 67 48 49 ≤ 1540873589717 := by decide +kernel

theorem rows22240R_1189 : rowsJ2 66 67 49 50 ≤ 2376229301448 := by decide +kernel

theorem rows22240R_1190 : rowsJ2 66 67 50 51 ≤ 3242346961121 := by decide +kernel

theorem rows22240R_1191 : rowsJ2 66 67 51 52 ≤ 4266116432695 := by decide +kernel

theorem rows22240R_1192 : rowsJ2 66 67 52 53 ≤ 5480581630728 := by decide +kernel

theorem rows22240R_1193 : rowsJ2 66 67 53 54 ≤ 6474101362033 := by decide +kernel

theorem rows22240R_1194 : rowsJ2 66 67 54 55 ≤ 7293338122374 := by decide +kernel

theorem rows22240R_1195 : rowsJ2 66 67 55 56 ≤ 8020784097942 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1186
#print axioms SieveCert.rows22240R_1195
