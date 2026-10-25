/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3367–3384 of 5796

File 295 of 465: the parts `rows22250R_3367` … `rows22250R_3384` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 92784 tests: row 110 columns 92–92, row 110 columns 93–93, row 110 columns
94–94, row 110 columns 95–95, row 110 columns 96–96, row 110 columns 97–97, row 110 columns 98–98, row 110 columns
99–99, row 110 columns 100–100, row 110 columns 101–101, row 110 columns 102–102, row 110 columns 103–103, row 110
columns 104–104, row 110 columns 105–105, row 110 columns 106–106, row 110 columns 107–107, row 110 columns 108–359,
row 111 columns 0–20), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3367 : rowsJ2 110 111 92 93 ≤ 1172642635006 := by decide +kernel

theorem rows22250R_3368 : rowsJ2 110 111 93 94 ≤ 1417382786187 := by decide +kernel

theorem rows22250R_3369 : rowsJ2 110 111 94 95 ≤ 1711813882603 := by decide +kernel

theorem rows22250R_3370 : rowsJ2 110 111 95 96 ≤ 2080612862091 := by decide +kernel

theorem rows22250R_3371 : rowsJ2 110 111 96 97 ≤ 2501418524642 := by decide +kernel

theorem rows22250R_3372 : rowsJ2 110 111 97 98 ≤ 2999731706377 := by decide +kernel

theorem rows22250R_3373 : rowsJ2 110 111 98 99 ≤ 3552742405346 := by decide +kernel

theorem rows22250R_3374 : rowsJ2 110 111 99 100 ≤ 4186826900275 := by decide +kernel

theorem rows22250R_3375 : rowsJ2 110 111 100 101 ≤ 4878713586424 := by decide +kernel

theorem rows22250R_3376 : rowsJ2 110 111 101 102 ≤ 5655710938454 := by decide +kernel

theorem rows22250R_3377 : rowsJ2 110 111 102 103 ≤ 6494074641600 := by decide +kernel

theorem rows22250R_3378 : rowsJ2 110 111 103 104 ≤ 7422108050252 := by decide +kernel

theorem rows22250R_3379 : rowsJ2 110 111 104 105 ≤ 8415585220184 := by decide +kernel

theorem rows22250R_3380 : rowsJ2 110 111 105 106 ≤ 9503873865191 := by decide +kernel

theorem rows22250R_3381 : rowsJ2 110 111 106 107 ≤ 10648261583248 := by decide +kernel

theorem rows22250R_3382 : rowsJ2 110 111 107 108 ≤ 11892945071497 := by decide +kernel

theorem rows22250R_3383 : rowsJ2 110 111 108 360 ≤ 248113195918265 := by decide +kernel

theorem rows22250R_3384 : rowsJ2 111 112 0 21 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3367
#print axioms SieveCert.rows22250R_3384
