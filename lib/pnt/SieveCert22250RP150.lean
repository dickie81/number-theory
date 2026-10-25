/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1743–1754 of 4715

File 150 of 351: the parts `rows22250R_1743` … `rows22250R_1754` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94946 tests: row 79 columns 50–50, row 79 columns 51–51, row 79 columns
52–52, row 79 columns 53–53, row 79 columns 54–54, row 79 columns 55–55, row 79 columns 56–56, row 79 columns 57–57,
row 79 columns 58–58, row 79 columns 59–59, row 79 columns 60–60, row 79 columns 61–61), each a sum of refined costs
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

theorem rows22250R_1743 : rowsJ2 79 80 50 51 ≤ 1512355776643 := by decide +kernel

theorem rows22250R_1744 : rowsJ2 79 80 51 52 ≤ 1342733409043 := by decide +kernel

theorem rows22250R_1745 : rowsJ2 79 80 52 53 ≤ 1169199185767 := by decide +kernel

theorem rows22250R_1746 : rowsJ2 79 80 53 54 ≤ 997470786257 := by decide +kernel

theorem rows22250R_1747 : rowsJ2 79 80 54 55 ≤ 821535222527 := by decide +kernel

theorem rows22250R_1748 : rowsJ2 79 80 55 56 ≤ 647256013985 := by decide +kernel

theorem rows22250R_1749 : rowsJ2 79 80 56 57 ≤ 530464619589 := by decide +kernel

theorem rows22250R_1750 : rowsJ2 79 80 57 58 ≤ 414718218214 := by decide +kernel

theorem rows22250R_1751 : rowsJ2 79 80 58 59 ≤ 356712604352 := by decide +kernel

theorem rows22250R_1752 : rowsJ2 79 80 59 60 ≤ 299223772163 := by decide +kernel

theorem rows22250R_1753 : rowsJ2 79 80 60 61 ≤ 240183312892 := by decide +kernel

theorem rows22250R_1754 : rowsJ2 79 80 61 62 ≤ 181612138341 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1743
#print axioms SieveCert.rows22250R_1754
