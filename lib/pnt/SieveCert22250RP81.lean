/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 866–873 of 4715

File 81 of 351: the parts `rows22250R_866` … `rows22250R_873` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 95784 in units of a depth-4 test: row 59 columns 51–51, row 59 columns
52–52, row 59 columns 53–53, row 59 columns 54–54, row 59 columns 55–55, row 59 columns 56–56, row 59 columns 57–57,
row 59 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_866 : rowsJ2 59 60 51 52 ≤ 5756437253784 := by decide +kernel

theorem rows22250R_867 : rowsJ2 59 60 52 53 ≤ 7064853968629 := by decide +kernel

theorem rows22250R_868 : rowsJ2 59 60 53 54 ≤ 8411947909398 := by decide +kernel

theorem rows22250R_869 : rowsJ2 59 60 54 55 ≤ 9796019211643 := by decide +kernel

theorem rows22250R_870 : rowsJ2 59 60 55 56 ≤ 11170792358894 := by decide +kernel

theorem rows22250R_871 : rowsJ2 59 60 56 57 ≤ 12360845011820 := by decide +kernel

theorem rows22250R_872 : rowsJ2 59 60 57 58 ≤ 13390359856393 := by decide +kernel

theorem rows22250R_873 : rowsJ2 59 60 58 59 ≤ 14527582964541 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_866
#print axioms SieveCert.rows22250R_873
