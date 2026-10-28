/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3374–3389 of 5066

File 273 of 387: the parts `rows22240R_3374` … `rows22240R_3389` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99782 in units of a depth-4 test: row 117 columns 76–78, row 117
columns 79–81, row 117 columns 82–84, row 117 columns 85–87, row 117 columns 88–89, row 117 columns 90–91, row 117
columns 92–93, row 117 columns 94–94, row 117 columns 95–95, row 117 columns 96–339, row 118 columns 0–26, row 118
columns 27–29, row 118 columns 30–31, row 118 columns 32–33, row 118 columns 34–35, row 118 columns 36–38), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3374 : rowsJ2 117 118 76 79 ≤ 0 := by decide +kernel

theorem rows22240R_3375 : rowsJ2 117 118 79 82 ≤ 251561071849 := by decide +kernel

theorem rows22240R_3376 : rowsJ2 117 118 82 85 ≤ 3166487572760 := by decide +kernel

theorem rows22240R_3377 : rowsJ2 117 118 85 88 ≤ 8507864891062 := by decide +kernel

theorem rows22240R_3378 : rowsJ2 117 118 88 90 ≤ 9846439149829 := by decide +kernel

theorem rows22240R_3379 : rowsJ2 117 118 90 92 ≤ 14084014011078 := by decide +kernel

theorem rows22240R_3380 : rowsJ2 117 118 92 94 ≤ 19153391017372 := by decide +kernel

theorem rows22240R_3381 : rowsJ2 117 118 94 95 ≤ 11761519038046 := by decide +kernel

theorem rows22240R_3382 : rowsJ2 117 118 95 96 ≤ 13354819580554 := by decide +kernel

theorem rows22240R_3383 : rowsJ2 117 118 96 340 ≤ 1444097862435717 := by decide +kernel

theorem rows22240R_3384 : rowsJ2 118 119 0 27 ≤ 1289782871556 := by decide +kernel

theorem rows22240R_3385 : rowsJ2 118 119 27 30 ≤ 9926477330748 := by decide +kernel

theorem rows22240R_3386 : rowsJ2 118 119 30 32 ≤ 14779770747814 := by decide +kernel

theorem rows22240R_3387 : rowsJ2 118 119 32 34 ≤ 20477549548949 := by decide +kernel

theorem rows22240R_3388 : rowsJ2 118 119 34 36 ≤ 16179444813510 := by decide +kernel

theorem rows22240R_3389 : rowsJ2 118 119 36 39 ≤ 16404247582762 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3374
#print axioms SieveCert.rows22240R_3389
