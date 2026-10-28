/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3739–3751 of 4715

File 287 of 351: the parts `rows22250R_3739` … `rows22250R_3751` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 98115 in units of a depth-4 test: row 140 columns 61–61, row 140
columns 62–62, row 140 columns 63–63, row 140 columns 64–64, row 140 columns 65–65, row 140 columns 66–66, row 140
columns 67–67, row 140 columns 68–68, row 140 columns 69–69, row 140 columns 70–70, row 140 columns 71–71, row 140
columns 72–73, row 140 columns 74–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3739 : rowsJ2 140 141 61 62 ≤ 11830097057696 := by decide +kernel

theorem rows22250R_3740 : rowsJ2 140 141 62 63 ≤ 12713267270675 := by decide +kernel

theorem rows22250R_3741 : rowsJ2 140 141 63 64 ≤ 11488729997295 := by decide +kernel

theorem rows22250R_3742 : rowsJ2 140 141 64 65 ≤ 10322116551767 := by decide +kernel

theorem rows22250R_3743 : rowsJ2 140 141 65 66 ≤ 9232322505025 := by decide +kernel

theorem rows22250R_3744 : rowsJ2 140 141 66 67 ≤ 8196044934487 := by decide +kernel

theorem rows22250R_3745 : rowsJ2 140 141 67 68 ≤ 7232641979924 := by decide +kernel

theorem rows22250R_3746 : rowsJ2 140 141 68 69 ≤ 6318797018453 := by decide +kernel

theorem rows22250R_3747 : rowsJ2 140 141 69 70 ≤ 5474321383736 := by decide +kernel

theorem rows22250R_3748 : rowsJ2 140 141 70 71 ≤ 4675846471569 := by decide +kernel

theorem rows22250R_3749 : rowsJ2 140 141 71 72 ≤ 3943631154421 := by decide +kernel

theorem rows22250R_3750 : rowsJ2 140 141 72 74 ≤ 5949927624899 := by decide +kernel

theorem rows22250R_3751 : rowsJ2 140 141 74 77 ≤ 5028193124830 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3739
#print axioms SieveCert.rows22250R_3751
