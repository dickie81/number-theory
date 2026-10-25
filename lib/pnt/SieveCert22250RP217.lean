/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2328–2341 of 5796

File 217 of 465: the parts `rows22250R_2328` … `rows22250R_2341` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 95663 tests: row 89 columns 53–53, row 89 columns 54–54, row 89 columns
55–55, row 89 columns 56–56, row 89 columns 57–57, row 89 columns 58–58, row 89 columns 59–59, row 89 columns 60–60,
row 89 columns 61–61, row 89 columns 62–62, row 89 columns 63–63, row 89 columns 64–64, row 89 columns 65–65, row 89
columns 66–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2328 : rowsJ2 89 90 53 54 ≤ 45562365006 := by decide +kernel

theorem rows22250R_2329 : rowsJ2 89 90 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2330 : rowsJ2 89 90 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2331 : rowsJ2 89 90 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2332 : rowsJ2 89 90 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2333 : rowsJ2 89 90 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2334 : rowsJ2 89 90 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2335 : rowsJ2 89 90 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2336 : rowsJ2 89 90 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2337 : rowsJ2 89 90 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2338 : rowsJ2 89 90 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_2339 : rowsJ2 89 90 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_2340 : rowsJ2 89 90 65 66 ≤ 0 := by decide +kernel

theorem rows22250R_2341 : rowsJ2 89 90 66 67 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2328
#print axioms SieveCert.rows22250R_2341
