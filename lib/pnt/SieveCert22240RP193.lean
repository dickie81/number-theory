/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2214–2227 of 5066

File 193 of 387: the parts `rows22240R_2214` … `rows22240R_2227` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96666 in units of a depth-4 test: row 88 columns 23–25, row 88 columns
26–30, row 88 columns 31–34, row 88 columns 35–37, row 88 columns 38–39, row 88 columns 40–40, row 88 columns 41–41,
row 88 columns 42–42, row 88 columns 43–43, row 88 columns 44–44, row 88 columns 45–45, row 88 columns 46–46, row 88
columns 47–47, row 88 columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_2214 : rowsJ2 88 89 23 26 ≤ 0 := by decide +kernel

theorem rows22240R_2215 : rowsJ2 88 89 26 31 ≤ 0 := by decide +kernel

theorem rows22240R_2216 : rowsJ2 88 89 31 35 ≤ 1621504211973 := by decide +kernel

theorem rows22240R_2217 : rowsJ2 88 89 35 38 ≤ 10157120170562 := by decide +kernel

theorem rows22240R_2218 : rowsJ2 88 89 38 40 ≤ 12396251367174 := by decide +kernel

theorem rows22240R_2219 : rowsJ2 88 89 40 41 ≤ 8096950859667 := by decide +kernel

theorem rows22240R_2220 : rowsJ2 88 89 41 42 ≤ 9422325651320 := by decide +kernel

theorem rows22240R_2221 : rowsJ2 88 89 42 43 ≤ 10762567371143 := by decide +kernel

theorem rows22240R_2222 : rowsJ2 88 89 43 44 ≤ 12114876310204 := by decide +kernel

theorem rows22240R_2223 : rowsJ2 88 89 44 45 ≤ 13476693985630 := by decide +kernel

theorem rows22240R_2224 : rowsJ2 88 89 45 46 ≤ 14720036901290 := by decide +kernel

theorem rows22240R_2225 : rowsJ2 88 89 46 47 ≤ 12374589084039 := by decide +kernel

theorem rows22240R_2226 : rowsJ2 88 89 47 48 ≤ 8995899872050 := by decide +kernel

theorem rows22240R_2227 : rowsJ2 88 89 48 49 ≤ 4287416474581 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2214
#print axioms SieveCert.rows22240R_2227
