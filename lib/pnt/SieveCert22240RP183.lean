/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2074–2088 of 5066

File 183 of 387: the parts `rows22240R_2074` … `rows22240R_2088` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98461 in units of a depth-4 test: row 84 columns 84–339, row 85 columns
0–16, row 85 columns 17–18, row 85 columns 19–20, row 85 columns 21–22, row 85 columns 23–24, row 85 columns 25–27,
row 85 columns 28–31, row 85 columns 32–35, row 85 columns 36–38, row 85 columns 39–40, row 85 columns 41–41, row 85
columns 42–42, row 85 columns 43–43, row 85 columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2074 : rowsJ2 84 85 84 340 ≤ 3863502382062 := by decide +kernel

theorem rows22240R_2075 : rowsJ2 85 86 0 17 ≤ 81783167552 := by decide +kernel

theorem rows22240R_2076 : rowsJ2 85 86 17 19 ≤ 8702186794 := by decide +kernel

theorem rows22240R_2077 : rowsJ2 85 86 19 21 ≤ 1928679741 := by decide +kernel

theorem rows22240R_2078 : rowsJ2 85 86 21 23 ≤ 0 := by decide +kernel

theorem rows22240R_2079 : rowsJ2 85 86 23 25 ≤ 0 := by decide +kernel

theorem rows22240R_2080 : rowsJ2 85 86 25 28 ≤ 0 := by decide +kernel

theorem rows22240R_2081 : rowsJ2 85 86 28 32 ≤ 0 := by decide +kernel

theorem rows22240R_2082 : rowsJ2 85 86 32 36 ≤ 2163720423718 := by decide +kernel

theorem rows22240R_2083 : rowsJ2 85 86 36 39 ≤ 10282579110991 := by decide +kernel

theorem rows22240R_2084 : rowsJ2 85 86 39 41 ≤ 11782485316258 := by decide +kernel

theorem rows22240R_2085 : rowsJ2 85 86 41 42 ≤ 7599957293872 := by decide +kernel

theorem rows22240R_2086 : rowsJ2 85 86 42 43 ≤ 8896154088571 := by decide +kernel

theorem rows22240R_2087 : rowsJ2 85 86 43 44 ≤ 7902007639849 := by decide +kernel

theorem rows22240R_2088 : rowsJ2 85 86 44 45 ≤ 6265291066219 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2074
#print axioms SieveCert.rows22240R_2088
