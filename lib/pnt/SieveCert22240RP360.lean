/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4616–4631 of 5066

File 360 of 387: the parts `rows22240R_4616` … `rows22240R_4631` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93929 in units of a depth-4 test: row 164 columns 55–55, row 164
columns 56–56, row 164 columns 57–57, row 164 columns 58–58, row 164 columns 59–60, row 164 columns 61–63, row 164
columns 64–339, row 165 columns 0–38, row 165 columns 39–41, row 165 columns 42–43, row 165 columns 44–44, row 165
columns 45–45, row 165 columns 46–46, row 165 columns 47–47, row 165 columns 48–48, row 165 columns 49–49), each a
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

theorem rows22240R_4616 : rowsJ2 164 165 55 56 ≤ 13081465187621 := by decide +kernel

theorem rows22240R_4617 : rowsJ2 164 165 56 57 ≤ 11527834670411 := by decide +kernel

theorem rows22240R_4618 : rowsJ2 164 165 57 58 ≤ 10082933106403 := by decide +kernel

theorem rows22240R_4619 : rowsJ2 164 165 58 59 ≤ 8743859551291 := by decide +kernel

theorem rows22240R_4620 : rowsJ2 164 165 59 61 ≤ 13880698220707 := by decide +kernel

theorem rows22240R_4621 : rowsJ2 164 165 61 64 ≤ 13282664269783 := by decide +kernel

theorem rows22240R_4622 : rowsJ2 164 165 64 340 ≤ 2600121652229664 := by decide +kernel

theorem rows22240R_4623 : rowsJ2 165 166 0 39 ≤ 11424878607466 := by decide +kernel

theorem rows22240R_4624 : rowsJ2 165 166 39 42 ≤ 18466611581621 := by decide +kernel

theorem rows22240R_4625 : rowsJ2 165 166 42 44 ≤ 18037663161811 := by decide +kernel

theorem rows22240R_4626 : rowsJ2 165 166 44 45 ≤ 10940588762522 := by decide +kernel

theorem rows22240R_4627 : rowsJ2 165 166 45 46 ≤ 12305705556144 := by decide +kernel

theorem rows22240R_4628 : rowsJ2 165 166 46 47 ≤ 13730774850665 := by decide +kernel

theorem rows22240R_4629 : rowsJ2 165 166 47 48 ≤ 15213705765189 := by decide +kernel

theorem rows22240R_4630 : rowsJ2 165 166 48 49 ≤ 16752703163277 := by decide +kernel

theorem rows22240R_4631 : rowsJ2 165 166 49 50 ≤ 18346178303153 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4616
#print axioms SieveCert.rows22240R_4631
