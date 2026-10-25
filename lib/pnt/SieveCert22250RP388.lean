/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4696–4710 of 5796

File 388 of 465: the parts `rows22250R_4696` … `rows22250R_4710` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98174 tests: row 151 columns 70–70, row 151 columns 71–71, row 151 columns
72–72, row 151 columns 73–73, row 151 columns 74–74, row 151 columns 75–75, row 151 columns 76–77, row 151 columns
78–80, row 151 columns 81–85, row 151 columns 86–359, row 152 columns 0–25, row 152 columns 26–49, row 152 columns
50–52, row 152 columns 53–54, row 152 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4696 : rowsJ2 151 152 70 71 ≤ 6828368587974 := by decide +kernel

theorem rows22250R_4697 : rowsJ2 151 152 71 72 ≤ 6001874296475 := by decide +kernel

theorem rows22250R_4698 : rowsJ2 151 152 72 73 ≤ 5232679449424 := by decide +kernel

theorem rows22250R_4699 : rowsJ2 151 152 73 74 ≤ 4519668332628 := by decide +kernel

theorem rows22250R_4700 : rowsJ2 151 152 74 75 ≤ 3861810092049 := by decide +kernel

theorem rows22250R_4701 : rowsJ2 151 152 75 76 ≤ 3258155962406 := by decide +kernel

theorem rows22250R_4702 : rowsJ2 151 152 76 78 ≤ 4917897464603 := by decide +kernel

theorem rows22250R_4703 : rowsJ2 151 152 78 81 ≤ 4158650275483 := by decide +kernel

theorem rows22250R_4704 : rowsJ2 151 152 81 86 ≤ 1704029318077 := by decide +kernel

theorem rows22250R_4705 : rowsJ2 151 152 86 360 ≤ 1059824678918144 := by decide +kernel

theorem rows22250R_4706 : rowsJ2 152 153 0 26 ≤ 864846723868 := by decide +kernel

theorem rows22250R_4707 : rowsJ2 152 153 26 50 ≤ 4634149028307 := by decide +kernel

theorem rows22250R_4708 : rowsJ2 152 153 50 53 ≤ 7657654020955 := by decide +kernel

theorem rows22250R_4709 : rowsJ2 152 153 53 55 ≤ 7985092633364 := by decide +kernel

theorem rows22250R_4710 : rowsJ2 152 153 55 56 ≤ 4984075076144 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4696
#print axioms SieveCert.rows22250R_4710
