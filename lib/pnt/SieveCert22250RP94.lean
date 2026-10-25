/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 884–894 of 5796

File 94 of 465: the parts `rows22250R_884` … `rows22250R_894` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98818 tests: row 59 columns 57–57, row 59 columns 58–58, row 59 columns
59–359, row 60 columns 0–15, row 60 columns 16–20, row 60 columns 21–23, row 60 columns 24–24, row 60 columns 25–25,
row 60 columns 26–26, row 60 columns 27–27, row 60 columns 28–28), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_884 : rowsJ2 59 60 57 58 ≤ 8715946910468 := by decide +kernel

theorem rows22250R_885 : rowsJ2 59 60 58 59 ≤ 10010039921573 := by decide +kernel

theorem rows22250R_886 : rowsJ2 59 60 59 360 ≤ 11279316931492 := by decide +kernel

theorem rows22250R_887 : rowsJ2 60 61 0 16 ≤ 2131252523767 := by decide +kernel

theorem rows22250R_888 : rowsJ2 60 61 16 21 ≤ 816722096677 := by decide +kernel

theorem rows22250R_889 : rowsJ2 60 61 21 24 ≤ 241665528009 := by decide +kernel

theorem rows22250R_890 : rowsJ2 60 61 24 25 ≤ 51361796209 := by decide +kernel

theorem rows22250R_891 : rowsJ2 60 61 25 26 ≤ 38515987595 := by decide +kernel

theorem rows22250R_892 : rowsJ2 60 61 26 27 ≤ 28837657299 := by decide +kernel

theorem rows22250R_893 : rowsJ2 60 61 27 28 ≤ 19239911791 := by decide +kernel

theorem rows22250R_894 : rowsJ2 60 61 28 29 ≤ 12805488904 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_884
#print axioms SieveCert.rows22250R_894
