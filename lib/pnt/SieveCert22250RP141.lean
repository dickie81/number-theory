/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1619–1630 of 4715

File 141 of 351: the parts `rows22250R_1619` … `rows22250R_1630` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94946 tests: row 76 columns 53–53, row 76 columns 54–54, row 76 columns
55–55, row 76 columns 56–56, row 76 columns 57–57, row 76 columns 58–58, row 76 columns 59–59, row 76 columns 60–60,
row 76 columns 61–61, row 76 columns 62–62, row 76 columns 63–63, row 76 columns 64–64), each a sum of refined costs
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

theorem rows22250R_1619 : rowsJ2 76 77 53 54 ≤ 2480062566437 := by decide +kernel

theorem rows22250R_1620 : rowsJ2 76 77 54 55 ≤ 2189800607083 := by decide +kernel

theorem rows22250R_1621 : rowsJ2 76 77 55 56 ≤ 1956584211920 := by decide +kernel

theorem rows22250R_1622 : rowsJ2 76 77 56 57 ≤ 1725721042038 := by decide +kernel

theorem rows22250R_1623 : rowsJ2 76 77 57 58 ≤ 1551953540493 := by decide +kernel

theorem rows22250R_1624 : rowsJ2 76 77 58 59 ≤ 1379889022647 := by decide +kernel

theorem rows22250R_1625 : rowsJ2 76 77 59 60 ≤ 1265107950995 := by decide +kernel

theorem rows22250R_1626 : rowsJ2 76 77 60 61 ≤ 1090325252675 := by decide +kernel

theorem rows22250R_1627 : rowsJ2 76 77 61 62 ≤ 973559759641 := by decide +kernel

theorem rows22250R_1628 : rowsJ2 76 77 62 63 ≤ 795658278204 := by decide +kernel

theorem rows22250R_1629 : rowsJ2 76 77 63 64 ≤ 676561536640 := by decide +kernel

theorem rows22250R_1630 : rowsJ2 76 77 64 65 ≤ 495127216691 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1619
#print axioms SieveCert.rows22250R_1630
