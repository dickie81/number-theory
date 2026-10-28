/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2320–2335 of 5066

File 201 of 387: the parts `rows22240R_2320` … `rows22240R_2335` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95817 in units of a depth-4 test: row 90 columns 51–51, row 90 columns
52–52, row 90 columns 53–53, row 90 columns 54–54, row 90 columns 55–55, row 90 columns 56–56, row 90 columns 57–57,
row 90 columns 58–59, row 90 columns 60–61, row 90 columns 62–63, row 90 columns 64–66, row 90 columns 67–70, row 90
columns 71–74, row 90 columns 75–77, row 90 columns 78–79, row 90 columns 80–80), each a sum of refined costs
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

theorem rows22240R_2320 : rowsJ2 90 91 51 52 ≤ 0 := by decide +kernel

theorem rows22240R_2321 : rowsJ2 90 91 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2322 : rowsJ2 90 91 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2323 : rowsJ2 90 91 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2324 : rowsJ2 90 91 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2325 : rowsJ2 90 91 56 57 ≤ 0 := by decide +kernel

theorem rows22240R_2326 : rowsJ2 90 91 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2327 : rowsJ2 90 91 58 60 ≤ 0 := by decide +kernel

theorem rows22240R_2328 : rowsJ2 90 91 60 62 ≤ 0 := by decide +kernel

theorem rows22240R_2329 : rowsJ2 90 91 62 64 ≤ 0 := by decide +kernel

theorem rows22240R_2330 : rowsJ2 90 91 64 67 ≤ 0 := by decide +kernel

theorem rows22240R_2331 : rowsJ2 90 91 67 71 ≤ 0 := by decide +kernel

theorem rows22240R_2332 : rowsJ2 90 91 71 75 ≤ 0 := by decide +kernel

theorem rows22240R_2333 : rowsJ2 90 91 75 78 ≤ 253871412611 := by decide +kernel

theorem rows22240R_2334 : rowsJ2 90 91 78 80 ≤ 1056307168357 := by decide +kernel

theorem rows22240R_2335 : rowsJ2 90 91 80 81 ≤ 1004853921278 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2320
#print axioms SieveCert.rows22240R_2335
