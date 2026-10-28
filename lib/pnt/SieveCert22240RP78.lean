/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 771–780 of 5066

File 78 of 387: the parts `rows22240R_771` … `rows22240R_780` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93448 in units of a depth-4 test: row 56 columns 46–46, row 56 columns
47–47, row 56 columns 48–48, row 56 columns 49–49, row 56 columns 50–50, row 56 columns 51–51, row 56 columns 52–52,
row 56 columns 53–53, row 56 columns 54–54, row 56 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_771 : rowsJ2 56 57 46 47 ≤ 414554259943 := by decide +kernel

theorem rows22240R_772 : rowsJ2 56 57 47 48 ≤ 885107826518 := by decide +kernel

theorem rows22240R_773 : rowsJ2 56 57 48 49 ≤ 1690998285259 := by decide +kernel

theorem rows22240R_774 : rowsJ2 56 57 49 50 ≤ 2607741284517 := by decide +kernel

theorem rows22240R_775 : rowsJ2 56 57 50 51 ≤ 3558243316038 := by decide +kernel

theorem rows22240R_776 : rowsJ2 56 57 51 52 ≤ 4681756907601 := by decide +kernel

theorem rows22240R_777 : rowsJ2 56 57 52 53 ≤ 6119262590128 := by decide +kernel

theorem rows22240R_778 : rowsJ2 56 57 53 54 ≤ 7574218222328 := by decide +kernel

theorem rows22240R_779 : rowsJ2 56 57 54 55 ≤ 9042094687707 := by decide +kernel

theorem rows22240R_780 : rowsJ2 56 57 55 56 ≤ 10618709442020 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_771
#print axioms SieveCert.rows22240R_780
