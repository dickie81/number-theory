/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3418–3433 of 5796

File 298 of 465: the parts `rows22250R_3418` … `rows22250R_3433` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95034 tests: row 111 columns 98–98, row 111 columns 99–99, row 111 columns
100–100, row 111 columns 101–101, row 111 columns 102–102, row 111 columns 103–103, row 111 columns 104–104, row 111
columns 105–105, row 111 columns 106–106, row 111 columns 107–107, row 111 columns 108–359, row 112 columns 0–22,
row 112 columns 23–31, row 112 columns 32–34, row 112 columns 35–36, row 112 columns 37–37), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3418 : rowsJ2 111 112 98 99 ≤ 3760756962525 := by decide +kernel

theorem rows22250R_3419 : rowsJ2 111 112 99 100 ≤ 4419035252008 := by decide +kernel

theorem rows22250R_3420 : rowsJ2 111 112 100 101 ≤ 5175657648583 := by decide +kernel

theorem rows22250R_3421 : rowsJ2 111 112 101 102 ≤ 5980068723394 := by decide +kernel

theorem rows22250R_3422 : rowsJ2 111 112 102 103 ≤ 6887485966496 := by decide +kernel

theorem rows22250R_3423 : rowsJ2 111 112 103 104 ≤ 7846547275666 := by decide +kernel

theorem rows22250R_3424 : rowsJ2 111 112 104 105 ≤ 8900131096728 := by decide +kernel

theorem rows22250R_3425 : rowsJ2 111 112 105 106 ≤ 10009481217108 := by decide +kernel

theorem rows22250R_3426 : rowsJ2 111 112 106 107 ≤ 11218769501429 := by decide +kernel

theorem rows22250R_3427 : rowsJ2 111 112 107 108 ≤ 12488548965789 := by decide +kernel

theorem rows22250R_3428 : rowsJ2 111 112 108 360 ≤ 346046549312466 := by decide +kernel

theorem rows22250R_3429 : rowsJ2 112 113 0 23 ≤ 0 := by decide +kernel

theorem rows22250R_3430 : rowsJ2 112 113 23 32 ≤ 2313556240802 := by decide +kernel

theorem rows22250R_3431 : rowsJ2 112 113 32 35 ≤ 10735253065041 := by decide +kernel

theorem rows22250R_3432 : rowsJ2 112 113 35 37 ≤ 14309289820589 := by decide +kernel

theorem rows22250R_3433 : rowsJ2 112 113 37 38 ≤ 9798797839209 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3418
#print axioms SieveCert.rows22250R_3433
