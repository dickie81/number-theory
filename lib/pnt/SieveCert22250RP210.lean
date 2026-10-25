/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2571–2585 of 4715

File 210 of 351: the parts `rows22250R_2571` … `rows22250R_2585` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95664 tests: row 99 columns 40–40, row 99 columns 41–41, row 99 columns
42–42, row 99 columns 43–43, row 99 columns 44–44, row 99 columns 45–45, row 99 columns 46–47, row 99 columns 48–49,
row 99 columns 50–51, row 99 columns 52–54, row 99 columns 55–59, row 99 columns 60–67, row 99 columns 68–73, row 99
columns 74–77, row 99 columns 78–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2571 : rowsJ2 99 100 40 41 ≤ 16414395300423 := by decide +kernel

theorem rows22250R_2572 : rowsJ2 99 100 41 42 ≤ 14443094109842 := by decide +kernel

theorem rows22250R_2573 : rowsJ2 99 100 42 43 ≤ 12664587746960 := by decide +kernel

theorem rows22250R_2574 : rowsJ2 99 100 43 44 ≤ 11010738674123 := by decide +kernel

theorem rows22250R_2575 : rowsJ2 99 100 44 45 ≤ 9438148157424 := by decide +kernel

theorem rows22250R_2576 : rowsJ2 99 100 45 46 ≤ 7946741207746 := by decide +kernel

theorem rows22250R_2577 : rowsJ2 99 100 46 48 ≤ 11744529129159 := by decide +kernel

theorem rows22250R_2578 : rowsJ2 99 100 48 50 ≤ 7160454674541 := by decide +kernel

theorem rows22250R_2579 : rowsJ2 99 100 50 52 ≤ 4009478385976 := by decide +kernel

theorem rows22250R_2580 : rowsJ2 99 100 52 55 ≤ 2257449436097 := by decide +kernel

theorem rows22250R_2581 : rowsJ2 99 100 55 60 ≤ 90987663668 := by decide +kernel

theorem rows22250R_2582 : rowsJ2 99 100 60 68 ≤ 0 := by decide +kernel

theorem rows22250R_2583 : rowsJ2 99 100 68 74 ≤ 0 := by decide +kernel

theorem rows22250R_2584 : rowsJ2 99 100 74 78 ≤ 357273623209 := by decide +kernel

theorem rows22250R_2585 : rowsJ2 99 100 78 80 ≤ 1217953714039 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2571
#print axioms SieveCert.rows22250R_2585
