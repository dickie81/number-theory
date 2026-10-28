/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 162–176 of 5066

File 11 of 387: the parts `rows22240R_162` … `rows22240R_176` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 94355 in units of a depth-4 test: row 32 columns 32–339, row 33 columns
0–13, row 33 columns 14–16, row 33 columns 17–18, row 33 columns 19–20, row 33 columns 21–21, row 33 columns 22–22,
row 33 columns 23–23, row 33 columns 24–24, row 33 columns 25–25, row 33 columns 26–26, row 33 columns 27–27, row 33
columns 28–28, row 33 columns 29–29, row 33 columns 30–30), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_162 : rowsJ2 32 33 32 340 ≤ 1038060759749 := by decide +kernel

theorem rows22240R_163 : rowsJ2 33 34 0 14 ≤ 866870159813 := by decide +kernel

theorem rows22240R_164 : rowsJ2 33 34 14 17 ≤ 1422696321178 := by decide +kernel

theorem rows22240R_165 : rowsJ2 33 34 17 19 ≤ 1926412761385 := by decide +kernel

theorem rows22240R_166 : rowsJ2 33 34 19 21 ≤ 2544994229900 := by decide +kernel

theorem rows22240R_167 : rowsJ2 33 34 21 22 ≤ 1392444222037 := by decide +kernel

theorem rows22240R_168 : rowsJ2 33 34 22 23 ≤ 1425892849024 := by decide +kernel

theorem rows22240R_169 : rowsJ2 33 34 23 24 ≤ 1448736278096 := by decide +kernel

theorem rows22240R_170 : rowsJ2 33 34 24 25 ≤ 1437411837722 := by decide +kernel

theorem rows22240R_171 : rowsJ2 33 34 25 26 ≤ 1394383567398 := by decide +kernel

theorem rows22240R_172 : rowsJ2 33 34 26 27 ≤ 1332472935073 := by decide +kernel

theorem rows22240R_173 : rowsJ2 33 34 27 28 ≤ 1263702097970 := by decide +kernel

theorem rows22240R_174 : rowsJ2 33 34 28 29 ≤ 1186877947251 := by decide +kernel

theorem rows22240R_175 : rowsJ2 33 34 29 30 ≤ 1110522628484 := by decide +kernel

theorem rows22240R_176 : rowsJ2 33 34 30 31 ≤ 1041832877030 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_162
#print axioms SieveCert.rows22240R_176
