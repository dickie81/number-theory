/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2654–2666 of 5796

File 243 of 465: the parts `rows22250R_2654` … `rows22250R_2666` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96270 tests: row 96 columns 43–43, row 96 columns 44–44, row 96 columns
45–45, row 96 columns 46–46, row 96 columns 47–47, row 96 columns 48–48, row 96 columns 49–49, row 96 columns 50–50,
row 96 columns 51–51, row 96 columns 52–52, row 96 columns 53–53, row 96 columns 54–54, row 96 columns 55–55), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2654 : rowsJ2 96 97 43 44 ≤ 10254057586352 := by decide +kernel

theorem rows22250R_2655 : rowsJ2 96 97 44 45 ≤ 11415381130315 := by decide +kernel

theorem rows22250R_2656 : rowsJ2 96 97 45 46 ≤ 12616203299799 := by decide +kernel

theorem rows22250R_2657 : rowsJ2 96 97 46 47 ≤ 13717901331489 := by decide +kernel

theorem rows22250R_2658 : rowsJ2 96 97 47 48 ≤ 14673727984644 := by decide +kernel

theorem rows22250R_2659 : rowsJ2 96 97 48 49 ≤ 13157761748970 := by decide +kernel

theorem rows22250R_2660 : rowsJ2 96 97 49 50 ≤ 11735901368200 := by decide +kernel

theorem rows22250R_2661 : rowsJ2 96 97 50 51 ≤ 8099459768006 := by decide +kernel

theorem rows22250R_2662 : rowsJ2 96 97 51 52 ≤ 4798928300237 := by decide +kernel

theorem rows22250R_2663 : rowsJ2 96 97 52 53 ≤ 2268325030436 := by decide +kernel

theorem rows22250R_2664 : rowsJ2 96 97 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2665 : rowsJ2 96 97 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2666 : rowsJ2 96 97 55 56 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2654
#print axioms SieveCert.rows22250R_2666
