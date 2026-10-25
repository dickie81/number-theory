/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 162–172 of 4715

File 11 of 351: the parts `rows22250R_162` … `rows22250R_172` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95044 tests: row 33 columns 28–28, row 33 columns 29–29, row 33 columns
30–30, row 33 columns 31–31, row 33 columns 32–32, row 33 columns 33–339, row 34 columns 0–13, row 34 columns 14–16,
row 34 columns 17–18, row 34 columns 19–20, row 34 columns 21–22), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_162 : rowsJ2 33 34 28 29 ≤ 873018602214 := by decide +kernel

theorem rows22250R_163 : rowsJ2 33 34 29 30 ≤ 814088460150 := by decide +kernel

theorem rows22250R_164 : rowsJ2 33 34 30 31 ≤ 783049849824 := by decide +kernel

theorem rows22250R_165 : rowsJ2 33 34 31 32 ≤ 770671280811 := by decide +kernel

theorem rows22250R_166 : rowsJ2 33 34 32 33 ≤ 804621572547 := by decide +kernel

theorem rows22250R_167 : rowsJ2 33 34 33 340 ≤ 878487432061 := by decide +kernel

theorem rows22250R_168 : rowsJ2 34 35 0 14 ≤ 760030616362 := by decide +kernel

theorem rows22250R_169 : rowsJ2 34 35 14 17 ≤ 2142971261873 := by decide +kernel

theorem rows22250R_170 : rowsJ2 34 35 17 19 ≤ 2215115364785 := by decide +kernel

theorem rows22250R_171 : rowsJ2 34 35 19 21 ≤ 2473642234162 := by decide +kernel

theorem rows22250R_172 : rowsJ2 34 35 21 23 ≤ 2484343564199 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_162
#print axioms SieveCert.rows22250R_172
