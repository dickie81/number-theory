/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4858–4874 of 5066

File 375 of 387: the parts `rows22240R_4858` … `rows22240R_4874` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96349 in units of a depth-4 test: row 178 columns 42–42, row 178
columns 43–43, row 178 columns 44–44, row 178 columns 45–45, row 178 columns 46–46, row 178 columns 47–47, row 178
columns 48–48, row 178 columns 49–94, row 178 columns 95–339, row 179 columns 0–34, row 179 columns 35–36, row 179
columns 37–38, row 179 columns 39–39, row 179 columns 40–40, row 179 columns 41–41, row 179 columns 42–42, row 179
columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4858 : rowsJ2 178 179 42 43 ≤ 22977585394182 := by decide +kernel

theorem rows22240R_4859 : rowsJ2 178 179 43 44 ≤ 25081385604675 := by decide +kernel

theorem rows22240R_4860 : rowsJ2 178 179 44 45 ≤ 27252628122023 := by decide +kernel

theorem rows22240R_4861 : rowsJ2 178 179 45 46 ≤ 24533988484616 := by decide +kernel

theorem rows22240R_4862 : rowsJ2 178 179 46 47 ≤ 21985447938628 := by decide +kernel

theorem rows22240R_4863 : rowsJ2 178 179 47 48 ≤ 19600741698108 := by decide +kernel

theorem rows22240R_4864 : rowsJ2 178 179 48 49 ≤ 17374095482902 := by decide +kernel

theorem rows22240R_4865 : rowsJ2 178 179 49 95 ≤ 28674349898578 := by decide +kernel

theorem rows22240R_4866 : rowsJ2 178 179 95 340 ≤ 2876643549254082 := by decide +kernel

theorem rows22240R_4867 : rowsJ2 179 180 0 35 ≤ 19261999795345 := by decide +kernel

theorem rows22240R_4868 : rowsJ2 179 180 35 37 ≤ 21056095887254 := by decide +kernel

theorem rows22240R_4869 : rowsJ2 179 180 37 39 ≤ 31210415660246 := by decide +kernel

theorem rows22240R_4870 : rowsJ2 179 180 39 40 ≤ 18408743231005 := by decide +kernel

theorem rows22240R_4871 : rowsJ2 179 180 40 41 ≤ 20379143433723 := by decide +kernel

theorem rows22240R_4872 : rowsJ2 179 180 41 42 ≤ 22422645660778 := by decide +kernel

theorem rows22240R_4873 : rowsJ2 179 180 42 43 ≤ 24537320721299 := by decide +kernel

theorem rows22240R_4874 : rowsJ2 179 180 43 44 ≤ 26721568985213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4858
#print axioms SieveCert.rows22240R_4874
