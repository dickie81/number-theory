/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 829–838 of 4715

File 78 of 351: the parts `rows22250R_829` … `rows22250R_838` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, work 99899 in units of a depth-4 test: row 58 columns 53–53, row 58 columns
54–54, row 58 columns 55–55, row 58 columns 56–56, row 58 columns 57–57, row 58 columns 58–339, row 59 columns 0–16,
row 59 columns 17–20, row 59 columns 21–22, row 59 columns 23–23), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_829 : rowsJ2 58 59 53 54 ≤ 8540217144361 := by decide +kernel

theorem rows22250R_830 : rowsJ2 58 59 54 55 ≤ 9987135165455 := by decide +kernel

theorem rows22250R_831 : rowsJ2 58 59 55 56 ≤ 11474964330904 := by decide +kernel

theorem rows22250R_832 : rowsJ2 58 59 56 57 ≤ 12729903894544 := by decide +kernel

theorem rows22250R_833 : rowsJ2 58 59 57 58 ≤ 13873922111014 := by decide +kernel

theorem rows22250R_834 : rowsJ2 58 59 58 340 ≤ 15080079961361 := by decide +kernel

theorem rows22250R_835 : rowsJ2 59 60 0 17 ≤ 2622227155522 := by decide +kernel

theorem rows22250R_836 : rowsJ2 59 60 17 21 ≤ 418687144849 := by decide +kernel

theorem rows22250R_837 : rowsJ2 59 60 21 23 ≤ 96019712730 := by decide +kernel

theorem rows22250R_838 : rowsJ2 59 60 23 24 ≤ 27404392532 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_829
#print axioms SieveCert.rows22250R_838
