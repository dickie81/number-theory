/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2474–2488 of 5796

File 228 of 465: the parts `rows22250R_2474` … `rows22250R_2488` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94768 tests: row 92 columns 55–55, row 92 columns 56–56, row 92 columns
57–57, row 92 columns 58–58, row 92 columns 59–59, row 92 columns 60–60, row 92 columns 61–61, row 92 columns 62–62,
row 92 columns 63–63, row 92 columns 64–65, row 92 columns 66–67, row 92 columns 68–69, row 92 columns 70–72, row 92
columns 73–76, row 92 columns 77–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2474 : rowsJ2 92 93 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2475 : rowsJ2 92 93 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2476 : rowsJ2 92 93 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2477 : rowsJ2 92 93 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2478 : rowsJ2 92 93 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2479 : rowsJ2 92 93 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2480 : rowsJ2 92 93 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2481 : rowsJ2 92 93 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2482 : rowsJ2 92 93 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_2483 : rowsJ2 92 93 64 66 ≤ 0 := by decide +kernel

theorem rows22250R_2484 : rowsJ2 92 93 66 68 ≤ 0 := by decide +kernel

theorem rows22250R_2485 : rowsJ2 92 93 68 70 ≤ 0 := by decide +kernel

theorem rows22250R_2486 : rowsJ2 92 93 70 73 ≤ 0 := by decide +kernel

theorem rows22250R_2487 : rowsJ2 92 93 73 77 ≤ 0 := by decide +kernel

theorem rows22250R_2488 : rowsJ2 92 93 77 81 ≤ 54259450345 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2474
#print axioms SieveCert.rows22250R_2488
