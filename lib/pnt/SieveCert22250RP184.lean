/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1889–1898 of 5796

File 184 of 465: the parts `rows22250R_1889` … `rows22250R_1898` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 93379 tests: row 80 columns 58–58, row 80 columns 59–59, row 80 columns
60–60, row 80 columns 61–61, row 80 columns 62–62, row 80 columns 63–63, row 80 columns 64–64, row 80 columns 65–65,
row 80 columns 66–66, row 80 columns 67–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1889 : rowsJ2 80 81 58 59 ≤ 1874324360160 := by decide +kernel

theorem rows22250R_1890 : rowsJ2 80 81 59 60 ≤ 1693075221872 := by decide +kernel

theorem rows22250R_1891 : rowsJ2 80 81 60 61 ≤ 1556829686669 := by decide +kernel

theorem rows22250R_1892 : rowsJ2 80 81 61 62 ≤ 1373163239777 := by decide +kernel

theorem rows22250R_1893 : rowsJ2 80 81 62 63 ≤ 1234966731534 := by decide +kernel

theorem rows22250R_1894 : rowsJ2 80 81 63 64 ≤ 1048500021317 := by decide +kernel

theorem rows22250R_1895 : rowsJ2 80 81 64 65 ≤ 908006140480 := by decide +kernel

theorem rows22250R_1896 : rowsJ2 80 81 65 66 ≤ 718346022878 := by decide +kernel

theorem rows22250R_1897 : rowsJ2 80 81 66 67 ≤ 575198420636 := by decide +kernel

theorem rows22250R_1898 : rowsJ2 80 81 67 68 ≤ 433055610858 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1889
#print axioms SieveCert.rows22250R_1898
