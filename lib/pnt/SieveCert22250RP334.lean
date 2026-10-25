/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3979–3994 of 5796

File 334 of 465: the parts `rows22250R_3979` … `rows22250R_3994` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98723 tests: row 128 columns 98–101, row 128 columns 102–359, row 129
columns 0–26, row 129 columns 27–29, row 129 columns 30–31, row 129 columns 32–34, row 129 columns 35–38, row 129
columns 39–47, row 129 columns 48–60, row 129 columns 61–62, row 129 columns 63–64, row 129 columns 65–65, row 129
columns 66–66, row 129 columns 67–67, row 129 columns 68–68, row 129 columns 69–69), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3979 : rowsJ2 128 129 98 102 ≤ 197594136143584 := by decide +kernel

theorem rows22250R_3980 : rowsJ2 128 129 102 360 ≤ 901450780823176 := by decide +kernel

theorem rows22250R_3981 : rowsJ2 129 130 0 27 ≤ 1265412320695 := by decide +kernel

theorem rows22250R_3982 : rowsJ2 129 130 27 30 ≤ 9328699639689 := by decide +kernel

theorem rows22250R_3983 : rowsJ2 129 130 30 32 ≤ 11978712784254 := by decide +kernel

theorem rows22250R_3984 : rowsJ2 129 130 32 35 ≤ 14043068362184 := by decide +kernel

theorem rows22250R_3985 : rowsJ2 129 130 35 39 ≤ 9391881273879 := by decide +kernel

theorem rows22250R_3986 : rowsJ2 129 130 39 48 ≤ 1978619612436 := by decide +kernel

theorem rows22250R_3987 : rowsJ2 129 130 48 61 ≤ 2657037966643 := by decide +kernel

theorem rows22250R_3988 : rowsJ2 129 130 61 63 ≤ 2913599531904 := by decide +kernel

theorem rows22250R_3989 : rowsJ2 129 130 63 65 ≤ 4390882596629 := by decide +kernel

theorem rows22250R_3990 : rowsJ2 129 130 65 66 ≤ 2702305091756 := by decide +kernel

theorem rows22250R_3991 : rowsJ2 129 130 66 67 ≤ 2981488338371 := by decide +kernel

theorem rows22250R_3992 : rowsJ2 129 130 67 68 ≤ 3202253968913 := by decide +kernel

theorem rows22250R_3993 : rowsJ2 129 130 68 69 ≤ 3382432482033 := by decide +kernel

theorem rows22250R_3994 : rowsJ2 129 130 69 70 ≤ 3502819476754 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3979
#print axioms SieveCert.rows22250R_3994
