/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4170–4183 of 5066

File 329 of 387: the parts `rows22240R_4170` … `rows22240R_4183` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98603 in units of a depth-4 test: row 145 columns 62–62, row 145
columns 63–63, row 145 columns 64–64, row 145 columns 65–65, row 145 columns 66–66, row 145 columns 67–67, row 145
columns 68–68, row 145 columns 69–69, row 145 columns 70–71, row 145 columns 72–73, row 145 columns 74–77, row 145
columns 78–339, row 146 columns 0–40, row 146 columns 41–47), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_4170 : rowsJ2 145 146 62 63 ≤ 12486338912695 := by decide +kernel

theorem rows22240R_4171 : rowsJ2 145 146 63 64 ≤ 11180073643594 := by decide +kernel

theorem rows22240R_4172 : rowsJ2 145 146 64 65 ≤ 9954550677686 := by decide +kernel

theorem rows22240R_4173 : rowsJ2 145 146 65 66 ≤ 8807747121085 := by decide +kernel

theorem rows22240R_4174 : rowsJ2 145 146 66 67 ≤ 7737781234958 := by decide +kernel

theorem rows22240R_4175 : rowsJ2 145 146 67 68 ≤ 6742901085030 := by decide +kernel

theorem rows22240R_4176 : rowsJ2 145 146 68 69 ≤ 5821483794838 := by decide +kernel

theorem rows22240R_4177 : rowsJ2 145 146 69 70 ≤ 4972034737154 := by decide +kernel

theorem rows22240R_4178 : rowsJ2 145 146 70 72 ≤ 7676829782453 := by decide +kernel

theorem rows22240R_4179 : rowsJ2 145 146 72 74 ≤ 5110377196814 := by decide +kernel

theorem rows22240R_4180 : rowsJ2 145 146 74 78 ≤ 4642186144760 := by decide +kernel

theorem rows22240R_4181 : rowsJ2 145 146 78 340 ≤ 1394574307030855 := by decide +kernel

theorem rows22240R_4182 : rowsJ2 146 147 0 41 ≤ 1623923799619 := by decide +kernel

theorem rows22240R_4183 : rowsJ2 146 147 41 48 ≤ 8533177246705 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4170
#print axioms SieveCert.rows22240R_4183
