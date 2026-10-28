/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2144–2160 of 5066

File 188 of 387: the parts `rows22240R_2144` … `rows22240R_2160` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96532 in units of a depth-4 test: row 86 columns 55–55, row 86 columns
56–56, row 86 columns 57–57, row 86 columns 58–58, row 86 columns 59–59, row 86 columns 60–60, row 86 columns 61–61,
row 86 columns 62–63, row 86 columns 64–65, row 86 columns 66–67, row 86 columns 68–70, row 86 columns 71–73, row 86
columns 74–76, row 86 columns 77–78, row 86 columns 79–79, row 86 columns 80–80, row 86 columns 81–81), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2144 : rowsJ2 86 87 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2145 : rowsJ2 86 87 56 57 ≤ 0 := by decide +kernel

theorem rows22240R_2146 : rowsJ2 86 87 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2147 : rowsJ2 86 87 58 59 ≤ 0 := by decide +kernel

theorem rows22240R_2148 : rowsJ2 86 87 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_2149 : rowsJ2 86 87 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_2150 : rowsJ2 86 87 61 62 ≤ 0 := by decide +kernel

theorem rows22240R_2151 : rowsJ2 86 87 62 64 ≤ 0 := by decide +kernel

theorem rows22240R_2152 : rowsJ2 86 87 64 66 ≤ 0 := by decide +kernel

theorem rows22240R_2153 : rowsJ2 86 87 66 68 ≤ 0 := by decide +kernel

theorem rows22240R_2154 : rowsJ2 86 87 68 71 ≤ 0 := by decide +kernel

theorem rows22240R_2155 : rowsJ2 86 87 71 74 ≤ 0 := by decide +kernel

theorem rows22240R_2156 : rowsJ2 86 87 74 77 ≤ 66050140729 := by decide +kernel

theorem rows22240R_2157 : rowsJ2 86 87 77 79 ≤ 1316057753543 := by decide +kernel

theorem rows22240R_2158 : rowsJ2 86 87 79 80 ≤ 1047138181381 := by decide +kernel

theorem rows22240R_2159 : rowsJ2 86 87 80 81 ≤ 1164297828589 := by decide +kernel

theorem rows22240R_2160 : rowsJ2 86 87 81 82 ≤ 1522705488908 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2144
#print axioms SieveCert.rows22240R_2160
