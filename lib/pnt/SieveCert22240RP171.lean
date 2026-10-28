/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1905–1916 of 5066

File 171 of 387: the parts `rows22240R_1905` … `rows22240R_1916` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 92216 in units of a depth-4 test: row 81 columns 41–41, row 81 columns
42–42, row 81 columns 43–43, row 81 columns 44–44, row 81 columns 45–45, row 81 columns 46–46, row 81 columns 47–47,
row 81 columns 48–48, row 81 columns 49–49, row 81 columns 50–50, row 81 columns 51–51, row 81 columns 52–52), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_1905 : rowsJ2 81 82 41 42 ≤ 1505989971048 := by decide +kernel

theorem rows22240R_1906 : rowsJ2 81 82 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1907 : rowsJ2 81 82 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1908 : rowsJ2 81 82 44 45 ≤ 58452386763 := by decide +kernel

theorem rows22240R_1909 : rowsJ2 81 82 45 46 ≤ 170940621547 := by decide +kernel

theorem rows22240R_1910 : rowsJ2 81 82 46 47 ≤ 333358166884 := by decide +kernel

theorem rows22240R_1911 : rowsJ2 81 82 47 48 ≤ 608005531494 := by decide +kernel

theorem rows22240R_1912 : rowsJ2 81 82 48 49 ≤ 894893449230 := by decide +kernel

theorem rows22240R_1913 : rowsJ2 81 82 49 50 ≤ 1068854712251 := by decide +kernel

theorem rows22240R_1914 : rowsJ2 81 82 50 51 ≤ 1017083392480 := by decide +kernel

theorem rows22240R_1915 : rowsJ2 81 82 51 52 ≤ 906076144832 := by decide +kernel

theorem rows22240R_1916 : rowsJ2 81 82 52 53 ≤ 796307192507 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1905
#print axioms SieveCert.rows22240R_1916
