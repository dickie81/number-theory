/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3710–3723 of 5066

File 295 of 387: the parts `rows22240R_3710` … `rows22240R_3723` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98515 in units of a depth-4 test: row 129 columns 63–63, row 129
columns 64–64, row 129 columns 65–65, row 129 columns 66–66, row 129 columns 67–67, row 129 columns 68–68, row 129
columns 69–69, row 129 columns 70–70, row 129 columns 71–71, row 129 columns 72–72, row 129 columns 73–73, row 129
columns 74–74, row 129 columns 75–75, row 129 columns 76–76), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3710 : rowsJ2 129 130 63 64 ≤ 6368211907419 := by decide +kernel

theorem rows22240R_3711 : rowsJ2 129 130 64 65 ≤ 6866514283111 := by decide +kernel

theorem rows22240R_3712 : rowsJ2 129 130 65 66 ≤ 7294829446017 := by decide +kernel

theorem rows22240R_3713 : rowsJ2 129 130 66 67 ≤ 7674336587047 := by decide +kernel

theorem rows22240R_3714 : rowsJ2 129 130 67 68 ≤ 7982251234430 := by decide +kernel

theorem rows22240R_3715 : rowsJ2 129 130 68 69 ≤ 8239780268062 := by decide +kernel

theorem rows22240R_3716 : rowsJ2 129 130 69 70 ≤ 7884292636810 := by decide +kernel

theorem rows22240R_3717 : rowsJ2 129 130 70 71 ≤ 7028163290155 := by decide +kernel

theorem rows22240R_3718 : rowsJ2 129 130 71 72 ≤ 6217050237480 := by decide +kernel

theorem rows22240R_3719 : rowsJ2 129 130 72 73 ≤ 5472021614400 := by decide +kernel

theorem rows22240R_3720 : rowsJ2 129 130 73 74 ≤ 4768777132518 := by decide +kernel

theorem rows22240R_3721 : rowsJ2 129 130 74 75 ≤ 4128837506643 := by decide +kernel

theorem rows22240R_3722 : rowsJ2 129 130 75 76 ≤ 3527769031870 := by decide +kernel

theorem rows22240R_3723 : rowsJ2 129 130 76 77 ≤ 2987552507155 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3710
#print axioms SieveCert.rows22240R_3723
