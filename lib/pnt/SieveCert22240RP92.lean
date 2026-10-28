/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 927–935 of 5066

File 92 of 387: the parts `rows22240R_927` … `rows22240R_935` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 91833 in units of a depth-4 test: row 60 columns 48–48, row 60 columns
49–49, row 60 columns 50–50, row 60 columns 51–51, row 60 columns 52–52, row 60 columns 53–53, row 60 columns 54–54,
row 60 columns 55–55, row 60 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_927 : rowsJ2 60 61 48 49 ≤ 1627569669200 := by decide +kernel

theorem rows22240R_928 : rowsJ2 60 61 49 50 ≤ 2509926034110 := by decide +kernel

theorem rows22240R_929 : rowsJ2 60 61 50 51 ≤ 3424775144540 := by decide +kernel

theorem rows22240R_930 : rowsJ2 60 61 51 52 ≤ 4506146226057 := by decide +kernel

theorem rows22240R_931 : rowsJ2 60 61 52 53 ≤ 5889731690673 := by decide +kernel

theorem rows22240R_932 : rowsJ2 60 61 53 54 ≤ 7290112564890 := by decide +kernel

theorem rows22240R_933 : rowsJ2 60 61 54 55 ≤ 8609935582608 := by decide +kernel

theorem rows22240R_934 : rowsJ2 60 61 55 56 ≤ 9847813893647 := by decide +kernel

theorem rows22240R_935 : rowsJ2 60 61 56 57 ≤ 11193841046597 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_927
#print axioms SieveCert.rows22240R_935
