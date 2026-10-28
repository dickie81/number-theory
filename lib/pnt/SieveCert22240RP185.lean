/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2101–2116 of 5066

File 185 of 387: the parts `rows22240R_2101` … `rows22240R_2116` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95493 in units of a depth-4 test: row 85 columns 57–57, row 85 columns
58–58, row 85 columns 59–59, row 85 columns 60–60, row 85 columns 61–61, row 85 columns 62–62, row 85 columns 63–64,
row 85 columns 65–66, row 85 columns 67–68, row 85 columns 69–71, row 85 columns 72–74, row 85 columns 75–77, row 85
columns 78–79, row 85 columns 80–80, row 85 columns 81–81, row 85 columns 82–82), each a sum of refined costs
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

theorem rows22240R_2101 : rowsJ2 85 86 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2102 : rowsJ2 85 86 58 59 ≤ 0 := by decide +kernel

theorem rows22240R_2103 : rowsJ2 85 86 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_2104 : rowsJ2 85 86 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_2105 : rowsJ2 85 86 61 62 ≤ 0 := by decide +kernel

theorem rows22240R_2106 : rowsJ2 85 86 62 63 ≤ 0 := by decide +kernel

theorem rows22240R_2107 : rowsJ2 85 86 63 65 ≤ 0 := by decide +kernel

theorem rows22240R_2108 : rowsJ2 85 86 65 67 ≤ 0 := by decide +kernel

theorem rows22240R_2109 : rowsJ2 85 86 67 69 ≤ 0 := by decide +kernel

theorem rows22240R_2110 : rowsJ2 85 86 69 72 ≤ 0 := by decide +kernel

theorem rows22240R_2111 : rowsJ2 85 86 72 75 ≤ 0 := by decide +kernel

theorem rows22240R_2112 : rowsJ2 85 86 75 78 ≤ 611823558785 := by decide +kernel

theorem rows22240R_2113 : rowsJ2 85 86 78 80 ≤ 2167185965236 := by decide +kernel

theorem rows22240R_2114 : rowsJ2 85 86 80 81 ≤ 1412988453191 := by decide +kernel

theorem rows22240R_2115 : rowsJ2 85 86 81 82 ≤ 1656613031572 := by decide +kernel

theorem rows22240R_2116 : rowsJ2 85 86 82 83 ≤ 2163253490162 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2101
#print axioms SieveCert.rows22240R_2116
