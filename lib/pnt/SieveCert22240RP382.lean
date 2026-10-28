/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4974–4989 of 5066

File 382 of 387: the parts `rows22240R_4974` … `rows22240R_4989` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94791 in units of a depth-4 test: row 189 columns 32–33, row 189
columns 34–35, row 189 columns 36–36, row 189 columns 37–37, row 189 columns 38–38, row 189 columns 39–339, row 190
columns 0–30, row 190 columns 31–33, row 190 columns 34–35, row 190 columns 36–36, row 190 columns 37–37, row 190
columns 38–339, row 191 columns 0–30, row 191 columns 31–33, row 191 columns 34–35, row 191 columns 36–36), each a
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

theorem rows22240R_4974 : rowsJ2 189 190 32 34 ≤ 26218547096993 := by decide +kernel

theorem rows22240R_4975 : rowsJ2 189 190 34 36 ≤ 40087919169960 := by decide +kernel

theorem rows22240R_4976 : rowsJ2 189 190 36 37 ≤ 26257050069992 := by decide +kernel

theorem rows22240R_4977 : rowsJ2 189 190 37 38 ≤ 30936762581567 := by decide +kernel

theorem rows22240R_4978 : rowsJ2 189 190 38 39 ≤ 33532600302843 := by decide +kernel

theorem rows22240R_4979 : rowsJ2 189 190 39 340 ≤ 4349563930914596 := by decide +kernel

theorem rows22240R_4980 : rowsJ2 190 191 0 31 ≤ 19432281371676 := by decide +kernel

theorem rows22240R_4981 : rowsJ2 190 191 31 34 ≤ 38605559100725 := by decide +kernel

theorem rows22240R_4982 : rowsJ2 190 191 34 36 ≤ 43337847113239 := by decide +kernel

theorem rows22240R_4983 : rowsJ2 190 191 36 37 ≤ 28165469494812 := by decide +kernel

theorem rows22240R_4984 : rowsJ2 190 191 37 38 ≤ 32969990276090 := by decide +kernel

theorem rows22240R_4985 : rowsJ2 190 191 38 340 ≤ 4480924644833266 := by decide +kernel

theorem rows22240R_4986 : rowsJ2 191 192 0 31 ≤ 22783365149452 := by decide +kernel

theorem rows22240R_4987 : rowsJ2 191 192 31 34 ≤ 42328638328991 := by decide +kernel

theorem rows22240R_4988 : rowsJ2 191 192 34 36 ≤ 46775462464848 := by decide +kernel

theorem rows22240R_4989 : rowsJ2 191 192 36 37 ≤ 30227878733950 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4974
#print axioms SieveCert.rows22240R_4989
