/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 709–719 of 5066

File 72 of 387: the parts `rows22240R_709` … `rows22240R_719` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 91767 in units of a depth-4 test: row 54 columns 53–53, row 54 columns
54–339, row 55 columns 0–14, row 55 columns 15–19, row 55 columns 20–22, row 55 columns 23–24, row 55 columns 25–25,
row 55 columns 26–26, row 55 columns 27–27, row 55 columns 28–28, row 55 columns 29–29), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_709 : rowsJ2 54 55 53 54 ≤ 7724740274127 := by decide +kernel

theorem rows22240R_710 : rowsJ2 54 55 54 340 ≤ 9221787773508 := by decide +kernel

theorem rows22240R_711 : rowsJ2 55 56 0 15 ≤ 2495928993536 := by decide +kernel

theorem rows22240R_712 : rowsJ2 55 56 15 20 ≤ 2157688458238 := by decide +kernel

theorem rows22240R_713 : rowsJ2 55 56 20 23 ≤ 802887466226 := by decide +kernel

theorem rows22240R_714 : rowsJ2 55 56 23 25 ≤ 368303795744 := by decide +kernel

theorem rows22240R_715 : rowsJ2 55 56 25 26 ≤ 144470413121 := by decide +kernel

theorem rows22240R_716 : rowsJ2 55 56 26 27 ≤ 120874565282 := by decide +kernel

theorem rows22240R_717 : rowsJ2 55 56 27 28 ≤ 103380105485 := by decide +kernel

theorem rows22240R_718 : rowsJ2 55 56 28 29 ≤ 84976948293 := by decide +kernel

theorem rows22240R_719 : rowsJ2 55 56 29 30 ≤ 68332855530 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_709
#print axioms SieveCert.rows22240R_719
