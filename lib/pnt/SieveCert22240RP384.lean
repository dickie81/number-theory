/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 5005–5021 of 5066

File 384 of 387: the parts `rows22240R_5005` … `rows22240R_5021` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 94483 in units of a depth-4 test: row 195 columns 33–339, row 196
columns 0–29, row 196 columns 30–80, row 196 columns 81–339, row 197 columns 0–28, row 197 columns 29–95, row 197
columns 96–339, row 198 columns 0–28, row 198 columns 29–339, row 199 columns 0–28, row 199 columns 29–339, row 200
columns 0–74, row 200 columns 75–339, row 201 columns 0–93, row 201 columns 94–339, rows 202–202, rows 203–203),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_5005 : rowsJ2 195 196 33 340 ≤ 5099133302625933 := by decide +kernel

theorem rows22240R_5006 : rowsJ2 196 197 0 30 ≤ 32036955271150 := by decide +kernel

theorem rows22240R_5007 : rowsJ2 196 197 30 81 ≤ 473403415415068 := by decide +kernel

theorem rows22240R_5008 : rowsJ2 196 197 81 340 ≤ 4777701575336757 := by decide +kernel

theorem rows22240R_5009 : rowsJ2 197 198 0 29 ≤ 24920275205640 := by decide +kernel

theorem rows22240R_5010 : rowsJ2 197 198 29 96 ≤ 1933617389279031 := by decide +kernel

theorem rows22240R_5011 : rowsJ2 197 198 96 340 ≤ 3433105976262404 := by decide +kernel

theorem rows22240R_5012 : rowsJ2 198 199 0 29 ≤ 28983208759678 := by decide +kernel

theorem rows22240R_5013 : rowsJ2 198 199 29 340 ≤ 5471744295160872 := by decide +kernel

theorem rows22240R_5014 : rowsJ2 199 200 0 29 ≤ 33545440872336 := by decide +kernel

theorem rows22240R_5015 : rowsJ2 199 200 29 340 ≤ 5577504042498367 := by decide +kernel

theorem rows22240R_5016 : rowsJ2 200 201 0 75 ≤ 258784104477126 := by decide +kernel

theorem rows22240R_5017 : rowsJ2 200 201 75 340 ≤ 5464498517468966 := by decide +kernel

theorem rows22240R_5018 : rowsJ2 201 202 0 94 ≤ 2125121760794452 := by decide +kernel

theorem rows22240R_5019 : rowsJ2 201 202 94 340 ≤ 3712209352826692 := by decide +kernel

theorem rows22240R_5020 : rows2 202 203 ≤ 5953219261544994 := by decide +kernel

theorem rows22240R_5021 : rows2 203 204 ≤ 6071655166145959 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_5005
#print axioms SieveCert.rows22240R_5021
