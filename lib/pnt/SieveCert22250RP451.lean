/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5568–5583 of 5796

File 451 of 465: the parts `rows22250R_5568` … `rows22250R_5583` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96282 tests: row 188 columns 50–50, row 188 columns 51–51, row 188 columns
52–359, row 189 columns 0–35, row 189 columns 36–37, row 189 columns 38–39, row 189 columns 40–40, row 189 columns
41–41, row 189 columns 42–42, row 189 columns 43–43, row 189 columns 44–44, row 189 columns 45–45, row 189 columns
46–46, row 189 columns 47–47, row 189 columns 48–48, row 189 columns 49–49), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5568 : rowsJ2 188 189 50 51 ≤ 15653100816247 := by decide +kernel

theorem rows22250R_5569 : rowsJ2 188 189 51 52 ≤ 13884290392689 := by decide +kernel

theorem rows22250R_5570 : rowsJ2 188 189 52 360 ≤ 2771867007312901 := by decide +kernel

theorem rows22250R_5571 : rowsJ2 189 190 0 36 ≤ 13292782615586 := by decide +kernel

theorem rows22250R_5572 : rowsJ2 189 190 36 38 ≤ 15445915599610 := by decide +kernel

theorem rows22250R_5573 : rowsJ2 189 190 38 40 ≤ 24309291217875 := by decide +kernel

theorem rows22250R_5574 : rowsJ2 189 190 40 41 ≤ 14929159048231 := by decide +kernel

theorem rows22250R_5575 : rowsJ2 189 190 41 42 ≤ 16535767771174 := by decide +kernel

theorem rows22250R_5576 : rowsJ2 189 190 42 43 ≤ 18202567527042 := by decide +kernel

theorem rows22250R_5577 : rowsJ2 189 190 43 44 ≤ 19927843857284 := by decide +kernel

theorem rows22250R_5578 : rowsJ2 189 190 44 45 ≤ 21710126893415 := by decide +kernel

theorem rows22250R_5579 : rowsJ2 189 190 45 46 ≤ 23548182065481 := by decide +kernel

theorem rows22250R_5580 : rowsJ2 189 190 46 47 ≤ 23302373182613 := by decide +kernel

theorem rows22250R_5581 : rowsJ2 189 190 47 48 ≤ 21037283646942 := by decide +kernel

theorem rows22250R_5582 : rowsJ2 189 190 48 49 ≤ 18909024842370 := by decide +kernel

theorem rows22250R_5583 : rowsJ2 189 190 49 50 ≤ 16912895528577 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5568
#print axioms SieveCert.rows22250R_5583
