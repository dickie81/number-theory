/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 728–739 of 5066

File 74 of 387: the parts `rows22240R_728` … `rows22240R_739` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 99168 in units of a depth-4 test: row 55 columns 38–38, row 55 columns
39–39, row 55 columns 40–40, row 55 columns 41–41, row 55 columns 42–42, row 55 columns 43–43, row 55 columns 44–44,
row 55 columns 45–45, row 55 columns 46–46, row 55 columns 47–47, row 55 columns 48–48, row 55 columns 49–49), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_728 : rowsJ2 55 56 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_729 : rowsJ2 55 56 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_730 : rowsJ2 55 56 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_731 : rowsJ2 55 56 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_732 : rowsJ2 55 56 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_733 : rowsJ2 55 56 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_734 : rowsJ2 55 56 44 45 ≤ 73404814694 := by decide +kernel

theorem rows22240R_735 : rowsJ2 55 56 45 46 ≤ 214668131500 := by decide +kernel

theorem rows22240R_736 : rowsJ2 55 56 46 47 ≤ 418632939077 := by decide +kernel

theorem rows22240R_737 : rowsJ2 55 56 47 48 ≤ 893816145722 := by decide +kernel

theorem rows22240R_738 : rowsJ2 55 56 48 49 ≤ 1707635526959 := by decide +kernel

theorem rows22240R_739 : rowsJ2 55 56 49 50 ≤ 2633398094715 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_728
#print axioms SieveCert.rows22240R_739
