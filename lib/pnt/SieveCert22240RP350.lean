/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4466–4481 of 5066

File 350 of 387: the parts `rows22240R_4466` … `rows22240R_4481` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95699 in units of a depth-4 test: row 157 columns 59–59, row 157
columns 60–60, row 157 columns 61–61, row 157 columns 62–62, row 157 columns 63–64, row 157 columns 65–67, row 157
columns 68–339, row 158 columns 0–40, row 158 columns 41–43, row 158 columns 44–45, row 158 columns 46–46, row 158
columns 47–47, row 158 columns 48–48, row 158 columns 49–49, row 158 columns 50–50, row 158 columns 51–51), each a
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

theorem rows22240R_4466 : rowsJ2 157 158 59 60 ≤ 10792284905453 := by decide +kernel

theorem rows22240R_4467 : rowsJ2 157 158 60 61 ≤ 9477342718324 := by decide +kernel

theorem rows22240R_4468 : rowsJ2 157 158 61 62 ≤ 8255801534440 := by decide +kernel

theorem rows22240R_4469 : rowsJ2 157 158 62 63 ≤ 7125407856596 := by decide +kernel

theorem rows22240R_4470 : rowsJ2 157 158 63 65 ≤ 11214008795941 := by decide +kernel

theorem rows22240R_4471 : rowsJ2 157 158 65 68 ≤ 10511113822734 := by decide +kernel

theorem rows22240R_4472 : rowsJ2 157 158 68 340 ≤ 2605216768328108 := by decide +kernel

theorem rows22240R_4473 : rowsJ2 158 159 0 41 ≤ 7034708363102 := by decide +kernel

theorem rows22240R_4474 : rowsJ2 158 159 41 44 ≤ 12198062692798 := by decide +kernel

theorem rows22240R_4475 : rowsJ2 158 159 44 46 ≤ 12663099456957 := by decide +kernel

theorem rows22240R_4476 : rowsJ2 158 159 46 47 ≤ 7884390906064 := by decide +kernel

theorem rows22240R_4477 : rowsJ2 158 159 47 48 ≤ 8998986001635 := by decide +kernel

theorem rows22240R_4478 : rowsJ2 158 159 48 49 ≤ 10170039709523 := by decide +kernel

theorem rows22240R_4479 : rowsJ2 158 159 49 50 ≤ 11395442753463 := by decide +kernel

theorem rows22240R_4480 : rowsJ2 158 159 50 51 ≤ 12673261905574 := by decide +kernel

theorem rows22240R_4481 : rowsJ2 158 159 51 52 ≤ 14001749988413 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4466
#print axioms SieveCert.rows22240R_4481
