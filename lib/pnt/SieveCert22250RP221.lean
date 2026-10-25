/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2381–2397 of 5796

File 221 of 465: the parts `rows22250R_2381` … `rows22250R_2397` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98833 tests: row 90 columns 58–58, row 90 columns 59–59, row 90 columns
60–60, row 90 columns 61–61, row 90 columns 62–62, row 90 columns 63–63, row 90 columns 64–64, row 90 columns 65–65,
row 90 columns 66–67, row 90 columns 68–69, row 90 columns 70–71, row 90 columns 72–74, row 90 columns 75–77, row 90
columns 78–80, row 90 columns 81–82, row 90 columns 83–83, row 90 columns 84–84), each a sum of refined costs
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

theorem rows22250R_2381 : rowsJ2 90 91 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2382 : rowsJ2 90 91 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2383 : rowsJ2 90 91 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2384 : rowsJ2 90 91 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2385 : rowsJ2 90 91 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2386 : rowsJ2 90 91 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_2387 : rowsJ2 90 91 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_2388 : rowsJ2 90 91 65 66 ≤ 0 := by decide +kernel

theorem rows22250R_2389 : rowsJ2 90 91 66 68 ≤ 0 := by decide +kernel

theorem rows22250R_2390 : rowsJ2 90 91 68 70 ≤ 0 := by decide +kernel

theorem rows22250R_2391 : rowsJ2 90 91 70 72 ≤ 0 := by decide +kernel

theorem rows22250R_2392 : rowsJ2 90 91 72 75 ≤ 0 := by decide +kernel

theorem rows22250R_2393 : rowsJ2 90 91 75 78 ≤ 0 := by decide +kernel

theorem rows22250R_2394 : rowsJ2 90 91 78 81 ≤ 55035701248 := by decide +kernel

theorem rows22250R_2395 : rowsJ2 90 91 81 83 ≤ 505981867311 := by decide +kernel

theorem rows22250R_2396 : rowsJ2 90 91 83 84 ≤ 668927155506 := by decide +kernel

theorem rows22250R_2397 : rowsJ2 90 91 84 85 ≤ 869374715448 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2381
#print axioms SieveCert.rows22250R_2397
