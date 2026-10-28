/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3739–3751 of 5066

File 297 of 387: the parts `rows22240R_3739` … `rows22240R_3751` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 98950 in units of a depth-4 test: row 130 columns 62–62, row 130
columns 63–63, row 130 columns 64–64, row 130 columns 65–65, row 130 columns 66–66, row 130 columns 67–67, row 130
columns 68–68, row 130 columns 69–69, row 130 columns 70–70, row 130 columns 71–71, row 130 columns 72–72, row 130
columns 73–73, row 130 columns 74–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3739 : rowsJ2 130 131 62 63 ≤ 6296173480470 := by decide +kernel

theorem rows22240R_3740 : rowsJ2 130 131 63 64 ≤ 6871863846175 := by decide +kernel

theorem rows22240R_3741 : rowsJ2 130 131 64 65 ≤ 7400163378727 := by decide +kernel

theorem rows22240R_3742 : rowsJ2 130 131 65 66 ≤ 7858918315251 := by decide +kernel

theorem rows22240R_3743 : rowsJ2 130 131 66 67 ≤ 8269195924364 := by decide +kernel

theorem rows22240R_3744 : rowsJ2 130 131 67 68 ≤ 8608372732299 := by decide +kernel

theorem rows22240R_3745 : rowsJ2 130 131 68 69 ≤ 8897537557216 := by decide +kernel

theorem rows22240R_3746 : rowsJ2 130 131 69 70 ≤ 7971338304211 := by decide +kernel

theorem rows22240R_3747 : rowsJ2 130 131 70 71 ≤ 7114307087299 := by decide +kernel

theorem rows22240R_3748 : rowsJ2 130 131 71 72 ≤ 6302387401181 := by decide +kernel

theorem rows22240R_3749 : rowsJ2 130 131 72 73 ≤ 5556512883221 := by decide +kernel

theorem rows22240R_3750 : rowsJ2 130 131 73 74 ≤ 4852515389167 := by decide +kernel

theorem rows22240R_3751 : rowsJ2 130 131 74 75 ≤ 4211789989239 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3739
#print axioms SieveCert.rows22240R_3751
