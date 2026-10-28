/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4892–4907 of 5066

File 377 of 387: the parts `rows22240R_4892` … `rows22240R_4907` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 92869 in units of a depth-4 test: row 180 columns 47–47, row 180
columns 48–339, row 181 columns 0–33, row 181 columns 34–36, row 181 columns 37–38, row 181 columns 39–39, row 181
columns 40–40, row 181 columns 41–41, row 181 columns 42–42, row 181 columns 43–43, row 181 columns 44–44, row 181
columns 45–45, row 181 columns 46–46, row 181 columns 47–339, row 182 columns 0–33, row 182 columns 34–35), each a
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

theorem rows22240R_4892 : rowsJ2 180 181 47 48 ≤ 18147102927735 := by decide +kernel

theorem rows22240R_4893 : rowsJ2 180 181 48 340 ≤ 3120776052140515 := by decide +kernel

theorem rows22240R_4894 : rowsJ2 181 182 0 34 ≤ 17125865851274 := by decide +kernel

theorem rows22240R_4895 : rowsJ2 181 182 34 37 ≤ 34002281406113 := by decide +kernel

theorem rows22240R_4896 : rowsJ2 181 182 37 39 ≤ 36531924377471 := by decide +kernel

theorem rows22240R_4897 : rowsJ2 181 182 39 40 ≤ 21314210232940 := by decide +kernel

theorem rows22240R_4898 : rowsJ2 181 182 40 41 ≤ 23448762025017 := by decide +kernel

theorem rows22240R_4899 : rowsJ2 181 182 41 42 ≤ 25657558470052 := by decide +kernel

theorem rows22240R_4900 : rowsJ2 181 182 42 43 ≤ 27938989501888 := by decide +kernel

theorem rows22240R_4901 : rowsJ2 181 182 43 44 ≤ 27627304792533 := by decide +kernel

theorem rows22240R_4902 : rowsJ2 181 182 44 45 ≤ 24808332495531 := by decide +kernel

theorem rows22240R_4903 : rowsJ2 181 182 45 46 ≤ 22169347230332 := by decide +kernel

theorem rows22240R_4904 : rowsJ2 181 182 46 47 ≤ 19703656518785 := by decide +kernel

theorem rows22240R_4905 : rowsJ2 181 182 47 340 ≤ 3261733517125811 := by decide +kernel

theorem rows22240R_4906 : rowsJ2 182 183 0 34 ≤ 20059975950614 := by decide +kernel

theorem rows22240R_4907 : rowsJ2 182 183 34 36 ≤ 21931596418124 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4892
#print axioms SieveCert.rows22240R_4907
