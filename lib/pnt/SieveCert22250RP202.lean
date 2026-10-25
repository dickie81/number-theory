/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2453–2465 of 4715

File 202 of 351: the parts `rows22250R_2453` … `rows22250R_2465` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 90521 tests: row 96 columns 51–52, row 96 columns 53–54, row 96 columns
55–57, row 96 columns 58–62, row 96 columns 63–69, row 96 columns 70–74, row 96 columns 75–77, row 96 columns 78–79,
row 96 columns 80–80, row 96 columns 81–81, row 96 columns 82–82, row 96 columns 83–83, row 96 columns 84–84), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2453 : rowsJ2 96 97 51 53 ≤ 5379277053376 := by decide +kernel

theorem rows22250R_2454 : rowsJ2 96 97 53 55 ≤ 1994899261208 := by decide +kernel

theorem rows22250R_2455 : rowsJ2 96 97 55 58 ≤ 177109963708 := by decide +kernel

theorem rows22250R_2456 : rowsJ2 96 97 58 63 ≤ 0 := by decide +kernel

theorem rows22250R_2457 : rowsJ2 96 97 63 70 ≤ 0 := by decide +kernel

theorem rows22250R_2458 : rowsJ2 96 97 70 75 ≤ 0 := by decide +kernel

theorem rows22250R_2459 : rowsJ2 96 97 75 78 ≤ 364767189489 := by decide +kernel

theorem rows22250R_2460 : rowsJ2 96 97 78 80 ≤ 1244753854861 := by decide +kernel

theorem rows22250R_2461 : rowsJ2 96 97 80 81 ≤ 1126277859936 := by decide +kernel

theorem rows22250R_2462 : rowsJ2 96 97 81 82 ≤ 1558065025606 := by decide +kernel

theorem rows22250R_2463 : rowsJ2 96 97 82 83 ≤ 2141506027610 := by decide +kernel

theorem rows22250R_2464 : rowsJ2 96 97 83 84 ≤ 2805858688640 := by decide +kernel

theorem rows22250R_2465 : rowsJ2 96 97 84 85 ≤ 3242782942468 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2453
#print axioms SieveCert.rows22250R_2465
