/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4721–4733 of 5796

File 390 of 465: the parts `rows22250R_4721` … `rows22250R_4733` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95535 tests: row 152 columns 66–66, row 152 columns 67–67, row 152 columns
68–68, row 152 columns 69–69, row 152 columns 70–70, row 152 columns 71–71, row 152 columns 72–72, row 152 columns
73–73, row 152 columns 74–74, row 152 columns 75–76, row 152 columns 77–78, row 152 columns 79–82, row 152 columns
83–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_4721 : rowsJ2 152 153 66 67 ≤ 10352578710957 := by decide +kernel

theorem rows22250R_4722 : rowsJ2 152 153 67 68 ≤ 9299322606144 := by decide +kernel

theorem rows22250R_4723 : rowsJ2 152 153 68 69 ≤ 8309014086982 := by decide +kernel

theorem rows22250R_4724 : rowsJ2 152 153 69 70 ≤ 7380179232950 := by decide +kernel

theorem rows22250R_4725 : rowsJ2 152 153 70 71 ≤ 6511443730779 := by decide +kernel

theorem rows22250R_4726 : rowsJ2 152 153 71 72 ≤ 5701528880903 := by decide +kernel

theorem rows22250R_4727 : rowsJ2 152 153 72 73 ≤ 4949247949912 := by decide +kernel

theorem rows22250R_4728 : rowsJ2 152 153 73 74 ≤ 4253502848978 := by decide +kernel

theorem rows22250R_4729 : rowsJ2 152 153 74 75 ≤ 3613281119943 := by decide +kernel

theorem rows22250R_4730 : rowsJ2 152 153 75 77 ≤ 5523423254498 := by decide +kernel

theorem rows22250R_4731 : rowsJ2 152 153 77 79 ≤ 3607091849028 := by decide +kernel

theorem rows22250R_4732 : rowsJ2 152 153 79 83 ≤ 3120053785780 := by decide +kernel

theorem rows22250R_4733 : rowsJ2 152 153 83 360 ≤ 1188083392694979 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4721
#print axioms SieveCert.rows22250R_4733
