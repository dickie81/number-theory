/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 755–766 of 4715

File 72 of 351: the parts `rows22250R_755` … `rows22250R_766` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 97582 in units of a depth-4 test: row 56 columns 54–54, row 56 columns
55–55, row 56 columns 56–339, row 57 columns 0–16, row 57 columns 17–20, row 57 columns 21–22, row 57 columns 23–23,
row 57 columns 24–24, row 57 columns 25–25, row 57 columns 26–26, row 57 columns 27–27, row 57 columns 28–28), each
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

theorem rows22250R_755 : rowsJ2 56 57 54 55 ≤ 10326901461172 := by decide +kernel

theorem rows22250R_756 : rowsJ2 56 57 55 56 ≤ 11992603910892 := by decide +kernel

theorem rows22250R_757 : rowsJ2 56 57 56 340 ≤ 13425736461820 := by decide +kernel

theorem rows22250R_758 : rowsJ2 57 58 0 17 ≤ 2964399501746 := by decide +kernel

theorem rows22250R_759 : rowsJ2 57 58 17 21 ≤ 607963244437 := by decide +kernel

theorem rows22250R_760 : rowsJ2 57 58 21 23 ≤ 163414658857 := by decide +kernel

theorem rows22250R_761 : rowsJ2 57 58 23 24 ≤ 54381582968 := by decide +kernel

theorem rows22250R_762 : rowsJ2 57 58 24 25 ≤ 40706053399 := by decide +kernel

theorem rows22250R_763 : rowsJ2 57 58 25 26 ≤ 28327457601 := by decide +kernel

theorem rows22250R_764 : rowsJ2 57 58 26 27 ≤ 19242150133 := by decide +kernel

theorem rows22250R_765 : rowsJ2 57 58 27 28 ≤ 9635068905 := by decide +kernel

theorem rows22250R_766 : rowsJ2 57 58 28 29 ≤ 4513132982 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_755
#print axioms SieveCert.rows22250R_766
