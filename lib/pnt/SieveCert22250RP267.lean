/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3458–3472 of 4715

File 267 of 351: the parts `rows22250R_3458` … `rows22250R_3472` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99994 tests: row 130 columns 55–56, row 130 columns 57–57, row 130 columns
58–58, row 130 columns 59–59, row 130 columns 60–60, row 130 columns 61–61, row 130 columns 62–62, row 130 columns
63–63, row 130 columns 64–64, row 130 columns 65–65, row 130 columns 66–66, row 130 columns 67–67, row 130 columns
68–68, row 130 columns 69–69, row 130 columns 70–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3458 : rowsJ2 130 131 55 57 ≤ 5079658510679 := by decide +kernel

theorem rows22250R_3459 : rowsJ2 130 131 57 58 ≤ 3374410821877 := by decide +kernel

theorem rows22250R_3460 : rowsJ2 130 131 58 59 ≤ 3989757189328 := by decide +kernel

theorem rows22250R_3461 : rowsJ2 130 131 59 60 ≤ 4647017105714 := by decide +kernel

theorem rows22250R_3462 : rowsJ2 130 131 60 61 ≤ 5322691533519 := by decide +kernel

theorem rows22250R_3463 : rowsJ2 130 131 61 62 ≤ 5950551234234 := by decide +kernel

theorem rows22250R_3464 : rowsJ2 130 131 62 63 ≤ 6508313604966 := by decide +kernel

theorem rows22250R_3465 : rowsJ2 130 131 63 64 ≤ 7017609577676 := by decide +kernel

theorem rows22250R_3466 : rowsJ2 130 131 64 65 ≤ 7455692468483 := by decide +kernel

theorem rows22250R_3467 : rowsJ2 130 131 65 66 ≤ 7844160339759 := by decide +kernel

theorem rows22250R_3468 : rowsJ2 130 131 66 67 ≤ 8159762853210 := by decide +kernel

theorem rows22250R_3469 : rowsJ2 130 131 67 68 ≤ 8424053373346 := by decide +kernel

theorem rows22250R_3470 : rowsJ2 130 131 68 69 ≤ 7517181547069 := by decide +kernel

theorem rows22250R_3471 : rowsJ2 130 131 69 70 ≤ 6680036905741 := by decide +kernel

theorem rows22250R_3472 : rowsJ2 130 131 70 71 ≤ 5888015059988 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3458
#print axioms SieveCert.rows22250R_3472
