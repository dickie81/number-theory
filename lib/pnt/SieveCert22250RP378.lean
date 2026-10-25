/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4573–4585 of 5796

File 378 of 465: the parts `rows22250R_4573` … `rows22250R_4585` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95709 tests: row 147 columns 69–69, row 147 columns 70–70, row 147 columns
71–71, row 147 columns 72–72, row 147 columns 73–73, row 147 columns 74–74, row 147 columns 75–75, row 147 columns
76–76, row 147 columns 77–77, row 147 columns 78–79, row 147 columns 80–81, row 147 columns 82–85, row 147 columns
86–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4573 : rowsJ2 147 148 69 70 ≤ 8845592076770 := by decide +kernel

theorem rows22250R_4574 : rowsJ2 147 148 70 71 ≤ 7962991142336 := by decide +kernel

theorem rows22250R_4575 : rowsJ2 147 148 71 72 ≤ 7121805528099 := by decide +kernel

theorem rows22250R_4576 : rowsJ2 147 148 72 73 ≤ 6337687775711 := by decide +kernel

theorem rows22250R_4577 : rowsJ2 147 148 73 74 ≤ 5592109323725 := by decide +kernel

theorem rows22250R_4578 : rowsJ2 147 148 74 75 ≤ 4901054521190 := by decide +kernel

theorem rows22250R_4579 : rowsJ2 147 148 75 76 ≤ 4245938263409 := by decide +kernel

theorem rows22250R_4580 : rowsJ2 147 148 76 77 ≤ 3643074195967 := by decide +kernel

theorem rows22250R_4581 : rowsJ2 147 148 77 78 ≤ 3073796623597 := by decide +kernel

theorem rows22250R_4582 : rowsJ2 147 148 78 80 ≤ 4639950816728 := by decide +kernel

theorem rows22250R_4583 : rowsJ2 147 148 80 82 ≤ 2956564245307 := by decide +kernel

theorem rows22250R_4584 : rowsJ2 147 148 82 86 ≤ 2391886115978 := by decide +kernel

theorem rows22250R_4585 : rowsJ2 147 148 86 360 ≤ 687921336647233 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4573
#print axioms SieveCert.rows22250R_4585
