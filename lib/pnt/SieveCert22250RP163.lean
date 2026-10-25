/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1930–1944 of 4715

File 163 of 351: the parts `rows22250R_1930` … `rows22250R_1944` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98007 tests: row 83 columns 81–81, row 83 columns 82–82, row 83 columns
83–339, row 84 columns 0–16, row 84 columns 17–19, row 84 columns 20–22, row 84 columns 23–25, row 84 columns 26–30,
row 84 columns 31–35, row 84 columns 36–37, row 84 columns 38–39, row 84 columns 40–40, row 84 columns 41–41, row 84
columns 42–42, row 84 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1930 : rowsJ2 83 84 81 82 ≤ 1722529860696 := by decide +kernel

theorem rows22250R_1931 : rowsJ2 83 84 82 83 ≤ 2330259942877 := by decide +kernel

theorem rows22250R_1932 : rowsJ2 83 84 83 340 ≤ 3089523466530 := by decide +kernel

theorem rows22250R_1933 : rowsJ2 84 85 0 17 ≤ 13425044815 := by decide +kernel

theorem rows22250R_1934 : rowsJ2 84 85 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_1935 : rowsJ2 84 85 20 23 ≤ 0 := by decide +kernel

theorem rows22250R_1936 : rowsJ2 84 85 23 26 ≤ 0 := by decide +kernel

theorem rows22250R_1937 : rowsJ2 84 85 26 31 ≤ 0 := by decide +kernel

theorem rows22250R_1938 : rowsJ2 84 85 31 36 ≤ 3132734696309 := by decide +kernel

theorem rows22250R_1939 : rowsJ2 84 85 36 38 ≤ 7290518610795 := by decide +kernel

theorem rows22250R_1940 : rowsJ2 84 85 38 40 ≤ 11472030592366 := by decide +kernel

theorem rows22250R_1941 : rowsJ2 84 85 40 41 ≤ 7520799250106 := by decide +kernel

theorem rows22250R_1942 : rowsJ2 84 85 41 42 ≤ 6823105480015 := by decide +kernel

theorem rows22250R_1943 : rowsJ2 84 85 42 43 ≤ 5466431020856 := by decide +kernel

theorem rows22250R_1944 : rowsJ2 84 85 43 44 ≤ 3009873922258 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1930
#print axioms SieveCert.rows22250R_1944
