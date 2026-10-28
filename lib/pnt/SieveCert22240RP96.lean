/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 971–978 of 5066

File 96 of 387: the parts `rows22240R_971` … `rows22240R_978` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 96594 in units of a depth-4 test: row 61 columns 51–51, row 61 columns
52–52, row 61 columns 53–53, row 61 columns 54–54, row 61 columns 55–55, row 61 columns 56–56, row 61 columns 57–57,
row 61 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_971 : rowsJ2 61 62 51 52 ≤ 4464282938765 := by decide +kernel

theorem rows22240R_972 : rowsJ2 61 62 52 53 ≤ 5835014529384 := by decide +kernel

theorem rows22240R_973 : rowsJ2 61 62 53 54 ≤ 7222385495814 := by decide +kernel

theorem rows22240R_974 : rowsJ2 61 62 54 55 ≤ 8435481909852 := by decide +kernel

theorem rows22240R_975 : rowsJ2 61 62 55 56 ≤ 9612383524079 := by decide +kernel

theorem rows22240R_976 : rowsJ2 61 62 56 57 ≤ 10847270103012 := by decide +kernel

theorem rows22240R_977 : rowsJ2 61 62 57 58 ≤ 11901975371056 := by decide +kernel

theorem rows22240R_978 : rowsJ2 61 62 58 59 ≤ 12726873835715 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_971
#print axioms SieveCert.rows22240R_978
