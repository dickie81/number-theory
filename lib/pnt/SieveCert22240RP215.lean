/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2494–2508 of 5066

File 215 of 387: the parts `rows22240R_2494` … `rows22240R_2508` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 94584 in units of a depth-4 test: row 94 columns 44–44, row 94 columns
45–45, row 94 columns 46–46, row 94 columns 47–47, row 94 columns 48–48, row 94 columns 49–49, row 94 columns 50–50,
row 94 columns 51–51, row 94 columns 52–52, row 94 columns 53–53, row 94 columns 54–55, row 94 columns 56–57, row 94
columns 58–59, row 94 columns 60–62, row 94 columns 63–67), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_2494 : rowsJ2 94 95 44 45 ≤ 16723535103484 := by decide +kernel

theorem rows22240R_2495 : rowsJ2 94 95 45 46 ≤ 14910424998013 := by decide +kernel

theorem rows22240R_2496 : rowsJ2 94 95 46 47 ≤ 13176501171892 := by decide +kernel

theorem rows22240R_2497 : rowsJ2 94 95 47 48 ≤ 11462032632203 := by decide +kernel

theorem rows22240R_2498 : rowsJ2 94 95 48 49 ≤ 9922068164268 := by decide +kernel

theorem rows22240R_2499 : rowsJ2 94 95 49 50 ≤ 8492541792687 := by decide +kernel

theorem rows22240R_2500 : rowsJ2 94 95 50 51 ≤ 7228784022263 := by decide +kernel

theorem rows22240R_2501 : rowsJ2 94 95 51 52 ≤ 6066499882972 := by decide +kernel

theorem rows22240R_2502 : rowsJ2 94 95 52 53 ≤ 3955906190697 := by decide +kernel

theorem rows22240R_2503 : rowsJ2 94 95 53 54 ≤ 2154064590294 := by decide +kernel

theorem rows22240R_2504 : rowsJ2 94 95 54 56 ≤ 963348018486 := by decide +kernel

theorem rows22240R_2505 : rowsJ2 94 95 56 58 ≤ 0 := by decide +kernel

theorem rows22240R_2506 : rowsJ2 94 95 58 60 ≤ 0 := by decide +kernel

theorem rows22240R_2507 : rowsJ2 94 95 60 63 ≤ 0 := by decide +kernel

theorem rows22240R_2508 : rowsJ2 94 95 63 68 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2494
#print axioms SieveCert.rows22240R_2508
