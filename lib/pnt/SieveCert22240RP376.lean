/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4875–4891 of 5066

File 376 of 387: the parts `rows22240R_4875` … `rows22240R_4891` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 97059 in units of a depth-4 test: row 179 columns 44–44, row 179
columns 45–45, row 179 columns 46–46, row 179 columns 47–47, row 179 columns 48–48, row 179 columns 49–339, row 180
columns 0–34, row 180 columns 35–36, row 180 columns 37–38, row 180 columns 39–39, row 180 columns 40–40, row 180
columns 41–41, row 180 columns 42–42, row 180 columns 43–43, row 180 columns 44–44, row 180 columns 45–45, row 180
columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_4875 : rowsJ2 179 180 44 45 ≤ 26426754826678 := by decide +kernel

theorem rows22240R_4876 : rowsJ2 179 180 45 46 ≤ 23734035955486 := by decide +kernel

theorem rows22240R_4877 : rowsJ2 179 180 46 47 ≤ 21212425246076 := by decide +kernel

theorem rows22240R_4878 : rowsJ2 179 180 47 48 ≤ 18855691778826 := by decide +kernel

theorem rows22240R_4879 : rowsJ2 179 180 48 49 ≤ 16658098607187 := by decide +kernel

theorem rows22240R_4880 : rowsJ2 179 180 49 340 ≤ 2978555618187077 := by decide +kernel

theorem rows22240R_4881 : rowsJ2 180 181 0 35 ≤ 22358619911459 := by decide +kernel

theorem rows22240R_4882 : rowsJ2 180 181 35 37 ≤ 23113912702464 := by decide +kernel

theorem rows22240R_4883 : rowsJ2 180 181 37 39 ≤ 33836969502760 := by decide +kernel

theorem rows22240R_4884 : rowsJ2 180 181 39 40 ≤ 19842328476201 := by decide +kernel

theorem rows22240R_4885 : rowsJ2 180 181 40 41 ≤ 21893372958349 := by decide +kernel

theorem rows22240R_4886 : rowsJ2 180 181 41 42 ≤ 24018035670211 := by decide +kernel

theorem rows22240R_4887 : rowsJ2 180 181 42 43 ≤ 26214542119552 := by decide +kernel

theorem rows22240R_4888 : rowsJ2 180 181 43 44 ≤ 28481452622862 := by decide +kernel

theorem rows22240R_4889 : rowsJ2 180 181 44 45 ≤ 25636101470133 := by decide +kernel

theorem rows22240R_4890 : rowsJ2 180 181 45 46 ≤ 22969655577321 := by decide +kernel

theorem rows22240R_4891 : rowsJ2 180 181 46 47 ≤ 20475387763394 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4875
#print axioms SieveCert.rows22240R_4891
