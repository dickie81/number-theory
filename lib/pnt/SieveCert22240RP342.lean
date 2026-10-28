/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4349–4365 of 5066

File 342 of 387: the parts `rows22240R_4349` … `rows22240R_4365` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 99265 in units of a depth-4 test: row 152 columns 62–62, row 152
columns 63–63, row 152 columns 64–64, row 152 columns 65–65, row 152 columns 66–67, row 152 columns 68–69, row 152
columns 70–73, row 152 columns 74–339, row 153 columns 0–42, row 153 columns 43–45, row 153 columns 46–47, row 153
columns 48–48, row 153 columns 49–49, row 153 columns 50–50, row 153 columns 51–51, row 153 columns 52–52, row 153
columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4349 : rowsJ2 152 153 62 63 ≤ 9287300340360 := by decide +kernel

theorem rows22240R_4350 : rowsJ2 152 153 63 64 ≤ 8126493991249 := by decide +kernel

theorem rows22240R_4351 : rowsJ2 152 153 64 65 ≤ 7049747515701 := by decide +kernel

theorem rows22240R_4352 : rowsJ2 152 153 65 66 ≤ 6055169664884 := by decide +kernel

theorem rows22240R_4353 : rowsJ2 152 153 66 68 ≤ 9446750066165 := by decide +kernel

theorem rows22240R_4354 : rowsJ2 152 153 68 70 ≤ 6413841804614 := by decide +kernel

theorem rows22240R_4355 : rowsJ2 152 153 70 74 ≤ 6128546485117 := by decide +kernel

theorem rows22240R_4356 : rowsJ2 152 153 74 340 ≤ 2146801934587603 := by decide +kernel

theorem rows22240R_4357 : rowsJ2 153 154 0 43 ≤ 5444124881488 := by decide +kernel

theorem rows22240R_4358 : rowsJ2 153 154 43 46 ≤ 9970404741731 := by decide +kernel

theorem rows22240R_4359 : rowsJ2 153 154 46 48 ≤ 10631081583892 := by decide +kernel

theorem rows22240R_4360 : rowsJ2 153 154 48 49 ≤ 6693218859647 := by decide +kernel

theorem rows22240R_4361 : rowsJ2 153 154 49 50 ≤ 7686481592319 := by decide +kernel

theorem rows22240R_4362 : rowsJ2 153 154 50 51 ≤ 8733001607697 := by decide +kernel

theorem rows22240R_4363 : rowsJ2 153 154 51 52 ≤ 9830734105726 := by decide +kernel

theorem rows22240R_4364 : rowsJ2 153 154 52 53 ≤ 10977784745250 := by decide +kernel

theorem rows22240R_4365 : rowsJ2 153 154 53 54 ≤ 12172409491244 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4349
#print axioms SieveCert.rows22240R_4365
