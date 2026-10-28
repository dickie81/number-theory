/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2173–2185 of 5066

File 190 of 387: the parts `rows22240R_2173` … `rows22240R_2185` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 95395 in units of a depth-4 test: row 87 columns 37–38, row 87 columns
39–40, row 87 columns 41–41, row 87 columns 42–42, row 87 columns 43–43, row 87 columns 44–44, row 87 columns 45–45,
row 87 columns 46–46, row 87 columns 47–47, row 87 columns 48–48, row 87 columns 49–49, row 87 columns 50–50, row 87
columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_2173 : rowsJ2 87 88 37 39 ≤ 9336125018689 := by decide +kernel

theorem rows22240R_2174 : rowsJ2 87 88 39 41 ≤ 13718364266056 := by decide +kernel

theorem rows22240R_2175 : rowsJ2 87 88 41 42 ≤ 8814045414002 := by decide +kernel

theorem rows22240R_2176 : rowsJ2 87 88 42 43 ≤ 10171973742333 := by decide +kernel

theorem rows22240R_2177 : rowsJ2 87 88 43 44 ≤ 11541888718987 := by decide +kernel

theorem rows22240R_2178 : rowsJ2 87 88 44 45 ≤ 12921218372340 := by decide +kernel

theorem rows22240R_2179 : rowsJ2 87 88 45 46 ≤ 10808605568077 := by decide +kernel

theorem rows22240R_2180 : rowsJ2 87 88 46 47 ≤ 8054432463956 := by decide +kernel

theorem rows22240R_2181 : rowsJ2 87 88 47 48 ≤ 4315628612277 := by decide +kernel

theorem rows22240R_2182 : rowsJ2 87 88 48 49 ≤ 0 := by decide +kernel

theorem rows22240R_2183 : rowsJ2 87 88 49 50 ≤ 0 := by decide +kernel

theorem rows22240R_2184 : rowsJ2 87 88 50 51 ≤ 0 := by decide +kernel

theorem rows22240R_2185 : rowsJ2 87 88 51 52 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2173
#print axioms SieveCert.rows22240R_2185
