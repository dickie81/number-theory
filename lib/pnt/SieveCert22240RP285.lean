/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3561–3576 of 5066

File 285 of 387: the parts `rows22240R_3561` … `rows22240R_3576` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97843 in units of a depth-4 test: row 124 columns 63–63, row 124
columns 64–64, row 124 columns 65–65, row 124 columns 66–66, row 124 columns 67–67, row 124 columns 68–68, row 124
columns 69–69, row 124 columns 70–70, row 124 columns 71–71, row 124 columns 72–72, row 124 columns 73–73, row 124
columns 74–74, row 124 columns 75–76, row 124 columns 77–78, row 124 columns 79–81, row 124 columns 82–84), each a
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

theorem rows22240R_3561 : rowsJ2 124 125 63 64 ≤ 4210261510106 := by decide +kernel

theorem rows22240R_3562 : rowsJ2 124 125 64 65 ≤ 4563148715866 := by decide +kernel

theorem rows22240R_3563 : rowsJ2 124 125 65 66 ≤ 4844015774480 := by decide +kernel

theorem rows22240R_3564 : rowsJ2 124 125 66 67 ≤ 5074596140620 := by decide +kernel

theorem rows22240R_3565 : rowsJ2 124 125 67 68 ≤ 5231318756458 := by decide +kernel

theorem rows22240R_3566 : rowsJ2 124 125 68 69 ≤ 5335967117314 := by decide +kernel

theorem rows22240R_3567 : rowsJ2 124 125 69 70 ≤ 5364462877713 := by decide +kernel

theorem rows22240R_3568 : rowsJ2 124 125 70 71 ≤ 5338443851003 := by decide +kernel

theorem rows22240R_3569 : rowsJ2 124 125 71 72 ≤ 5233115431127 := by decide +kernel

theorem rows22240R_3570 : rowsJ2 124 125 72 73 ≤ 4492550668785 := by decide +kernel

theorem rows22240R_3571 : rowsJ2 124 125 73 74 ≤ 3793265822720 := by decide +kernel

theorem rows22240R_3572 : rowsJ2 124 125 74 75 ≤ 3157451514135 := by decide +kernel

theorem rows22240R_3573 : rowsJ2 124 125 75 77 ≤ 4583503901066 := by decide +kernel

theorem rows22240R_3574 : rowsJ2 124 125 77 79 ≤ 2603587413107 := by decide +kernel

theorem rows22240R_3575 : rowsJ2 124 125 79 82 ≤ 1503164931327 := by decide +kernel

theorem rows22240R_3576 : rowsJ2 124 125 82 85 ≤ 5444971294855 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3561
#print axioms SieveCert.rows22240R_3576
