/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5785–5795 of 5796

File 465 of 465: the parts `rows22250R_5785` … `rows22250R_5795` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 70056 tests: rows 285–286, rows 287–288, rows 289–339, rows 340–342, rows
343–345, rows 346–348, rows 349–350, rows 351–352, rows 353–354, rows 355–356, rows 357–359), each a sum of refined
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

theorem rows22250R_5785 : rows2 285 287 ≤ 19896788266543606 := by decide +kernel

theorem rows22250R_5786 : rows2 287 289 ≤ 19999772500999701 := by decide +kernel

theorem rows22250R_5787 : rows2 289 340 ≤ 29903034514516853 := by decide +kernel

theorem rows22250R_5788 : rows2 340 343 ≤ 30301298306004456 := by decide +kernel

theorem rows22250R_5789 : rows2 343 346 ≤ 31593891180789321 := by decide +kernel

theorem rows22250R_5790 : rows2 346 349 ≤ 33039847764328712 := by decide +kernel

theorem rows22250R_5791 : rows2 349 351 ≤ 22863590323868771 := by decide +kernel

theorem rows22250R_5792 : rows2 351 353 ≤ 23575680716961537 := by decide +kernel

theorem rows22250R_5793 : rows2 353 355 ≤ 24334375429910484 := by decide +kernel

theorem rows22250R_5794 : rows2 355 357 ≤ 25135874965929432 := by decide +kernel

theorem rows22250R_5795 : rows2 357 360 ≤ 39287033968739487 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5785
#print axioms SieveCert.rows22250R_5795
