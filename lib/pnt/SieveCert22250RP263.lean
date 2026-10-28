/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3398–3412 of 4715

File 263 of 351: the parts `rows22250R_3398` … `rows22250R_3412` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 98752 in units of a depth-4 test: row 128 columns 0–24, row 128 columns
25–28, row 128 columns 29–37, row 128 columns 38–54, row 128 columns 55–57, row 128 columns 58–58, row 128 columns
59–59, row 128 columns 60–60, row 128 columns 61–61, row 128 columns 62–62, row 128 columns 63–63, row 128 columns
64–64, row 128 columns 65–65, row 128 columns 66–66, row 128 columns 67–67), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3398 : rowsJ2 128 129 0 25 ≤ 4653336282411 := by decide +kernel

theorem rows22250R_3399 : rowsJ2 128 129 25 29 ≤ 15019962504132 := by decide +kernel

theorem rows22250R_3400 : rowsJ2 128 129 29 38 ≤ 8248865790594 := by decide +kernel

theorem rows22250R_3401 : rowsJ2 128 129 38 55 ≤ 3620851789741 := by decide +kernel

theorem rows22250R_3402 : rowsJ2 128 129 55 58 ≤ 6678493564653 := by decide +kernel

theorem rows22250R_3403 : rowsJ2 128 129 58 59 ≤ 3277179109302 := by decide +kernel

theorem rows22250R_3404 : rowsJ2 128 129 59 60 ≤ 3875288120624 := by decide +kernel

theorem rows22250R_3405 : rowsJ2 128 129 60 61 ≤ 4492184626417 := by decide +kernel

theorem rows22250R_3406 : rowsJ2 128 129 61 62 ≤ 5060833780635 := by decide +kernel

theorem rows22250R_3407 : rowsJ2 128 129 62 63 ≤ 5558649378009 := by decide +kernel

theorem rows22250R_3408 : rowsJ2 128 129 63 64 ≤ 6007460256118 := by decide +kernel

theorem rows22250R_3409 : rowsJ2 128 129 64 65 ≤ 6384210166530 := by decide +kernel

theorem rows22250R_3410 : rowsJ2 128 129 65 66 ≤ 6710693795505 := by decide +kernel

theorem rows22250R_3411 : rowsJ2 128 129 66 67 ≤ 6963344324748 := by decide +kernel

theorem rows22250R_3412 : rowsJ2 128 129 67 68 ≤ 7163909808162 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3398
#print axioms SieveCert.rows22250R_3412
