/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2260–2274 of 5796

File 212 of 465: the parts `rows22250R_2260` … `rows22250R_2274` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97798 tests: row 88 columns 21–22, row 88 columns 23–24, row 88 columns
25–27, row 88 columns 28–30, row 88 columns 31–34, row 88 columns 35–37, row 88 columns 38–39, row 88 columns 40–41,
row 88 columns 42–42, row 88 columns 43–43, row 88 columns 44–44, row 88 columns 45–45, row 88 columns 46–46, row 88
columns 47–47, row 88 columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2260 : rowsJ2 88 89 21 23 ≤ 0 := by decide +kernel

theorem rows22250R_2261 : rowsJ2 88 89 23 25 ≤ 0 := by decide +kernel

theorem rows22250R_2262 : rowsJ2 88 89 25 28 ≤ 0 := by decide +kernel

theorem rows22250R_2263 : rowsJ2 88 89 28 31 ≤ 0 := by decide +kernel

theorem rows22250R_2264 : rowsJ2 88 89 31 35 ≤ 0 := by decide +kernel

theorem rows22250R_2265 : rowsJ2 88 89 35 38 ≤ 2578899582223 := by decide +kernel

theorem rows22250R_2266 : rowsJ2 88 89 38 40 ≤ 5112395454703 := by decide +kernel

theorem rows22250R_2267 : rowsJ2 88 89 40 42 ≤ 8725964151858 := by decide +kernel

theorem rows22250R_2268 : rowsJ2 88 89 42 43 ≤ 4513439444678 := by decide +kernel

theorem rows22250R_2269 : rowsJ2 88 89 43 44 ≤ 3487643579817 := by decide +kernel

theorem rows22250R_2270 : rowsJ2 88 89 44 45 ≤ 2164223859465 := by decide +kernel

theorem rows22250R_2271 : rowsJ2 88 89 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_2272 : rowsJ2 88 89 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2273 : rowsJ2 88 89 47 48 ≤ 89621011951 := by decide +kernel

theorem rows22250R_2274 : rowsJ2 88 89 48 49 ≤ 315664894293 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2260
#print axioms SieveCert.rows22250R_2274
