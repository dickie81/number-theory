/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 165–179 of 5796

File 11 of 465: the parts `rows22250R_165` … `rows22250R_179` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97061 tests: row 33 columns 17–18, row 33 columns 19–20, row 33 columns
21–21, row 33 columns 22–22, row 33 columns 23–23, row 33 columns 24–24, row 33 columns 25–25, row 33 columns 26–26,
row 33 columns 27–27, row 33 columns 28–28, row 33 columns 29–29, row 33 columns 30–30, row 33 columns 31–31, row 33
columns 32–32, row 33 columns 33–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_165 : rowsJ2 33 34 17 19 ≤ 1540052354223 := by decide +kernel

theorem rows22250R_166 : rowsJ2 33 34 19 21 ≤ 2034116630854 := by decide +kernel

theorem rows22250R_167 : rowsJ2 33 34 21 22 ≤ 1112589042600 := by decide +kernel

theorem rows22250R_168 : rowsJ2 33 34 22 23 ≤ 1138929509667 := by decide +kernel

theorem rows22250R_169 : rowsJ2 33 34 23 24 ≤ 1156855214190 := by decide +kernel

theorem rows22250R_170 : rowsJ2 33 34 24 25 ≤ 1147404186272 := by decide +kernel

theorem rows22250R_171 : rowsJ2 33 34 25 26 ≤ 1112705296628 := by decide +kernel

theorem rows22250R_172 : rowsJ2 33 34 26 27 ≤ 1062887423243 := by decide +kernel

theorem rows22250R_173 : rowsJ2 33 34 27 28 ≤ 1007705323871 := by decide +kernel

theorem rows22250R_174 : rowsJ2 33 34 28 29 ≤ 943465499551 := by decide +kernel

theorem rows22250R_175 : rowsJ2 33 34 29 30 ≤ 874928846625 := by decide +kernel

theorem rows22250R_176 : rowsJ2 33 34 30 31 ≤ 809727441948 := by decide +kernel

theorem rows22250R_177 : rowsJ2 33 34 31 32 ≤ 755696770083 := by decide +kernel

theorem rows22250R_178 : rowsJ2 33 34 32 33 ≤ 716875098884 := by decide +kernel

theorem rows22250R_179 : rowsJ2 33 34 33 360 ≤ 699988756062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_165
#print axioms SieveCert.rows22250R_179
