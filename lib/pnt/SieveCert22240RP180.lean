/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2031–2045 of 5066

File 180 of 387: the parts `rows22240R_2031` … `rows22240R_2045` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 94484 in units of a depth-4 test: row 84 columns 19–20, row 84 columns
21–22, row 84 columns 23–24, row 84 columns 25–27, row 84 columns 28–30, row 84 columns 31–34, row 84 columns 35–37,
row 84 columns 38–39, row 84 columns 40–40, row 84 columns 41–41, row 84 columns 42–42, row 84 columns 43–43, row 84
columns 44–44, row 84 columns 45–45, row 84 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2031 : rowsJ2 84 85 19 21 ≤ 5770624427 := by decide +kernel

theorem rows22240R_2032 : rowsJ2 84 85 21 23 ≤ 0 := by decide +kernel

theorem rows22240R_2033 : rowsJ2 84 85 23 25 ≤ 0 := by decide +kernel

theorem rows22240R_2034 : rowsJ2 84 85 25 28 ≤ 0 := by decide +kernel

theorem rows22240R_2035 : rowsJ2 84 85 28 31 ≤ 0 := by decide +kernel

theorem rows22240R_2036 : rowsJ2 84 85 31 35 ≤ 864074271183 := by decide +kernel

theorem rows22240R_2037 : rowsJ2 84 85 35 38 ≤ 6119130344585 := by decide +kernel

theorem rows22240R_2038 : rowsJ2 84 85 38 40 ≤ 9091778073521 := by decide +kernel

theorem rows22240R_2039 : rowsJ2 84 85 40 41 ≤ 5991219645409 := by decide +kernel

theorem rows22240R_2040 : rowsJ2 84 85 41 42 ≤ 7090560890730 := by decide +kernel

theorem rows22240R_2041 : rowsJ2 84 85 42 43 ≤ 6555579643955 := by decide +kernel

theorem rows22240R_2042 : rowsJ2 84 85 43 44 ≤ 5186728467825 := by decide +kernel

theorem rows22240R_2043 : rowsJ2 84 85 44 45 ≤ 3210990712871 := by decide +kernel

theorem rows22240R_2044 : rowsJ2 84 85 45 46 ≤ 167015174245 := by decide +kernel

theorem rows22240R_2045 : rowsJ2 84 85 46 47 ≤ 219883100311 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2031
#print axioms SieveCert.rows22240R_2045
