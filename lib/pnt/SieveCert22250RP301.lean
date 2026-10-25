/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3467–3483 of 5796

File 301 of 465: the parts `rows22250R_3467` … `rows22250R_3483` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99885 tests: row 112 columns 105–105, row 112 columns 106–106, row 112
columns 107–359, row 113 columns 0–23, row 113 columns 24–31, row 113 columns 32–33, row 113 columns 34–35, row 113
columns 36–36, row 113 columns 37–37, row 113 columns 38–38, row 113 columns 39–39, row 113 columns 40–40, row 113
columns 41–41, row 113 columns 42–42, row 113 columns 43–44, row 113 columns 45–46, row 113 columns 47–48), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_3467 : rowsJ2 112 113 105 106 ≤ 10568266624842 := by decide +kernel

theorem rows22250R_3468 : rowsJ2 112 113 106 107 ≤ 11801875689194 := by decide +kernel

theorem rows22250R_3469 : rowsJ2 112 113 107 360 ≤ 540698950152866 := by decide +kernel

theorem rows22250R_3470 : rowsJ2 113 114 0 24 ≤ 0 := by decide +kernel

theorem rows22250R_3471 : rowsJ2 113 114 24 32 ≤ 2841293220170 := by decide +kernel

theorem rows22250R_3472 : rowsJ2 113 114 32 34 ≤ 6609658461605 := by decide +kernel

theorem rows22250R_3473 : rowsJ2 113 114 34 36 ≤ 11942425217467 := by decide +kernel

theorem rows22250R_3474 : rowsJ2 113 114 36 37 ≤ 8535536847042 := by decide +kernel

theorem rows22250R_3475 : rowsJ2 113 114 37 38 ≤ 10199457169131 := by decide +kernel

theorem rows22250R_3476 : rowsJ2 113 114 38 39 ≤ 12146736907849 := by decide +kernel

theorem rows22250R_3477 : rowsJ2 113 114 39 40 ≤ 12657509386036 := by decide +kernel

theorem rows22250R_3478 : rowsJ2 113 114 40 41 ≤ 10945813191653 := by decide +kernel

theorem rows22250R_3479 : rowsJ2 113 114 41 42 ≤ 9401877588796 := by decide +kernel

theorem rows22250R_3480 : rowsJ2 113 114 42 43 ≤ 8021730927227 := by decide +kernel

theorem rows22250R_3481 : rowsJ2 113 114 43 45 ≤ 12454570384041 := by decide +kernel

theorem rows22250R_3482 : rowsJ2 113 114 45 47 ≤ 8143564671290 := by decide +kernel

theorem rows22250R_3483 : rowsJ2 113 114 47 49 ≤ 4493709658865 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3467
#print axioms SieveCert.rows22250R_3483
