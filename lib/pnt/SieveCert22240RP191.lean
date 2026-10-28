/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2186–2201 of 5066

File 191 of 387: the parts `rows22240R_2186` … `rows22240R_2201` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 98212 in units of a depth-4 test: row 87 columns 52–52, row 87 columns
53–53, row 87 columns 54–54, row 87 columns 55–55, row 87 columns 56–56, row 87 columns 57–57, row 87 columns 58–58,
row 87 columns 59–59, row 87 columns 60–60, row 87 columns 61–62, row 87 columns 63–64, row 87 columns 65–66, row 87
columns 67–69, row 87 columns 70–73, row 87 columns 74–76, row 87 columns 77–78), each a sum of refined costs
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

theorem rows22240R_2186 : rowsJ2 87 88 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2187 : rowsJ2 87 88 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2188 : rowsJ2 87 88 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2189 : rowsJ2 87 88 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2190 : rowsJ2 87 88 56 57 ≤ 0 := by decide +kernel

theorem rows22240R_2191 : rowsJ2 87 88 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2192 : rowsJ2 87 88 58 59 ≤ 0 := by decide +kernel

theorem rows22240R_2193 : rowsJ2 87 88 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_2194 : rowsJ2 87 88 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_2195 : rowsJ2 87 88 61 63 ≤ 0 := by decide +kernel

theorem rows22240R_2196 : rowsJ2 87 88 63 65 ≤ 0 := by decide +kernel

theorem rows22240R_2197 : rowsJ2 87 88 65 67 ≤ 0 := by decide +kernel

theorem rows22240R_2198 : rowsJ2 87 88 67 70 ≤ 0 := by decide +kernel

theorem rows22240R_2199 : rowsJ2 87 88 70 74 ≤ 0 := by decide +kernel

theorem rows22240R_2200 : rowsJ2 87 88 74 77 ≤ 65448611624 := by decide +kernel

theorem rows22240R_2201 : rowsJ2 87 88 77 79 ≤ 967612489203 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2186
#print axioms SieveCert.rows22240R_2201
