/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1672–1687 of 4715

File 145 of 351: the parts `rows22250R_1672` … `rows22250R_1687` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 96721 in units of a depth-4 test: row 77 columns 63–63, row 77 columns
64–64, row 77 columns 65–65, row 77 columns 66–66, row 77 columns 67–67, row 77 columns 68–69, row 77 columns 70–71,
row 77 columns 72–73, row 77 columns 74–76, row 77 columns 77–339, row 78 columns 0–17, row 78 columns 18–19, row 78
columns 20–21, row 78 columns 22–23, row 78 columns 24–25, row 78 columns 26–27), each a sum of refined costs
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

theorem rows22250R_1672 : rowsJ2 77 78 63 64 ≤ 431514021081 := by decide +kernel

theorem rows22250R_1673 : rowsJ2 77 78 64 65 ≤ 309392714640 := by decide +kernel

theorem rows22250R_1674 : rowsJ2 77 78 65 66 ≤ 188091287515 := by decide +kernel

theorem rows22250R_1675 : rowsJ2 77 78 66 67 ≤ 63135270428 := by decide +kernel

theorem rows22250R_1676 : rowsJ2 77 78 67 68 ≤ 0 := by decide +kernel

theorem rows22250R_1677 : rowsJ2 77 78 68 70 ≤ 0 := by decide +kernel

theorem rows22250R_1678 : rowsJ2 77 78 70 72 ≤ 0 := by decide +kernel

theorem rows22250R_1679 : rowsJ2 77 78 72 74 ≤ 0 := by decide +kernel

theorem rows22250R_1680 : rowsJ2 77 78 74 77 ≤ 128374824714 := by decide +kernel

theorem rows22250R_1681 : rowsJ2 77 78 77 340 ≤ 292269625632 := by decide +kernel

theorem rows22250R_1682 : rowsJ2 78 79 0 18 ≤ 170930053847 := by decide +kernel

theorem rows22250R_1683 : rowsJ2 78 79 18 20 ≤ 15250150691 := by decide +kernel

theorem rows22250R_1684 : rowsJ2 78 79 20 22 ≤ 8293741758 := by decide +kernel

theorem rows22250R_1685 : rowsJ2 78 79 22 24 ≤ 1076293096 := by decide +kernel

theorem rows22250R_1686 : rowsJ2 78 79 24 26 ≤ 0 := by decide +kernel

theorem rows22250R_1687 : rowsJ2 78 79 26 28 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1672
#print axioms SieveCert.rows22250R_1687
