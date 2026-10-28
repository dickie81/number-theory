/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4774–4789 of 5066

File 370 of 387: the parts `rows22240R_4774` … `rows22240R_4789` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93150 in units of a depth-4 test: row 173 columns 39–40, row 173
columns 41–41, row 173 columns 42–42, row 173 columns 43–43, row 173 columns 44–44, row 173 columns 45–45, row 173
columns 46–46, row 173 columns 47–47, row 173 columns 48–48, row 173 columns 49–49, row 173 columns 50–50, row 173
columns 51–51, row 173 columns 52–52, row 173 columns 53–54, row 173 columns 55–339, row 174 columns 0–35), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_4774 : rowsJ2 173 174 39 41 ≤ 24255366781025 := by decide +kernel

theorem rows22240R_4775 : rowsJ2 173 174 41 42 ≤ 14492153176631 := by decide +kernel

theorem rows22240R_4776 : rowsJ2 173 174 42 43 ≤ 16161862035129 := by decide +kernel

theorem rows22240R_4777 : rowsJ2 173 174 43 44 ≤ 17898545541943 := by decide +kernel

theorem rows22240R_4778 : rowsJ2 173 174 44 45 ≤ 19700105376985 := by decide +kernel

theorem rows22240R_4779 : rowsJ2 173 174 45 46 ≤ 21564726270470 := by decide +kernel

theorem rows22240R_4780 : rowsJ2 173 174 46 47 ≤ 23490901009019 := by decide +kernel

theorem rows22240R_4781 : rowsJ2 173 174 47 48 ≤ 23240049709318 := by decide +kernel

theorem rows22240R_4782 : rowsJ2 173 174 48 49 ≤ 20881142897805 := by decide +kernel

theorem rows22240R_4783 : rowsJ2 173 174 49 50 ≤ 18670183833748 := by decide +kernel

theorem rows22240R_4784 : rowsJ2 173 174 50 51 ≤ 16602071040639 := by decide +kernel

theorem rows22240R_4785 : rowsJ2 173 174 51 52 ≤ 14672119481745 := by decide +kernel

theorem rows22240R_4786 : rowsJ2 173 174 52 53 ≤ 12876018300142 := by decide +kernel

theorem rows22240R_4787 : rowsJ2 173 174 53 55 ≤ 20879643333902 := by decide +kernel

theorem rows22240R_4788 : rowsJ2 173 174 55 340 ≤ 2741898054035962 := by decide +kernel

theorem rows22240R_4789 : rowsJ2 174 175 0 36 ≤ 13447273265143 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4774
#print axioms SieveCert.rows22240R_4789
