/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2637–2642 of 5796

File 241 of 465: the parts `rows22250R_2637` … `rows22250R_2642` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 88427 tests: row 95 columns 88–88, row 95 columns 89–89, row 95 columns
90–90, row 95 columns 91–91, row 95 columns 92–92, row 95 columns 93–93), each a sum of refined costs (`rows2` or
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

theorem rows22250R_2637 : rowsJ2 95 96 88 89 ≤ 2722775286614 := by decide +kernel

theorem rows22250R_2638 : rowsJ2 95 96 89 90 ≤ 3482096061312 := by decide +kernel

theorem rows22250R_2639 : rowsJ2 95 96 90 91 ≤ 4387205133401 := by decide +kernel

theorem rows22250R_2640 : rowsJ2 95 96 91 92 ≤ 5435631474285 := by decide +kernel

theorem rows22250R_2641 : rowsJ2 95 96 92 93 ≤ 6415345486504 := by decide +kernel

theorem rows22250R_2642 : rowsJ2 95 96 93 94 ≤ 6500284330039 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2637
#print axioms SieveCert.rows22250R_2642
