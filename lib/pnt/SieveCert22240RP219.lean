/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2547–2561 of 5066

File 219 of 387: the parts `rows22240R_2547` … `rows22240R_2561` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 92886 in units of a depth-4 test: row 95 columns 51–51, row 95 columns
52–52, row 95 columns 53–54, row 95 columns 55–56, row 95 columns 57–58, row 95 columns 59–61, row 95 columns 62–66,
row 95 columns 67–71, row 95 columns 72–75, row 95 columns 76–78, row 95 columns 79–79, row 95 columns 80–80, row 95
columns 81–81, row 95 columns 82–82, row 95 columns 83–83), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_2547 : rowsJ2 95 96 51 52 ≤ 5349296286160 := by decide +kernel

theorem rows22240R_2548 : rowsJ2 95 96 52 53 ≤ 4322796371036 := by decide +kernel

theorem rows22240R_2549 : rowsJ2 95 96 53 55 ≤ 4042817389224 := by decide +kernel

theorem rows22240R_2550 : rowsJ2 95 96 55 57 ≤ 493675940180 := by decide +kernel

theorem rows22240R_2551 : rowsJ2 95 96 57 59 ≤ 0 := by decide +kernel

theorem rows22240R_2552 : rowsJ2 95 96 59 62 ≤ 0 := by decide +kernel

theorem rows22240R_2553 : rowsJ2 95 96 62 67 ≤ 0 := by decide +kernel

theorem rows22240R_2554 : rowsJ2 95 96 67 72 ≤ 0 := by decide +kernel

theorem rows22240R_2555 : rowsJ2 95 96 72 76 ≤ 0 := by decide +kernel

theorem rows22240R_2556 : rowsJ2 95 96 76 79 ≤ 619871992580 := by decide +kernel

theorem rows22240R_2557 : rowsJ2 95 96 79 80 ≤ 631688787966 := by decide +kernel

theorem rows22240R_2558 : rowsJ2 95 96 80 81 ≤ 960112005016 := by decide +kernel

theorem rows22240R_2559 : rowsJ2 95 96 81 82 ≤ 1426182535344 := by decide +kernel

theorem rows22240R_2560 : rowsJ2 95 96 82 83 ≤ 2055706653808 := by decide +kernel

theorem rows22240R_2561 : rowsJ2 95 96 83 84 ≤ 2844276726133 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2547
#print axioms SieveCert.rows22240R_2561
