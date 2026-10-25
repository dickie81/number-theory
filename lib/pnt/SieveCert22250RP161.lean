/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1901–1913 of 4715

File 161 of 351: the parts `rows22250R_1901` … `rows22250R_1913` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97110 tests: row 83 columns 41–41, row 83 columns 42–42, row 83 columns
43–43, row 83 columns 44–44, row 83 columns 45–45, row 83 columns 46–46, row 83 columns 47–47, row 83 columns 48–48,
row 83 columns 49–49, row 83 columns 50–50, row 83 columns 51–51, row 83 columns 52–52, row 83 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1901 : rowsJ2 83 84 41 42 ≤ 4466997469142 := by decide +kernel

theorem rows22250R_1902 : rowsJ2 83 84 42 43 ≤ 2817045336929 := by decide +kernel

theorem rows22250R_1903 : rowsJ2 83 84 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1904 : rowsJ2 83 84 44 45 ≤ 56743642439 := by decide +kernel

theorem rows22250R_1905 : rowsJ2 83 84 45 46 ≤ 168401634239 := by decide +kernel

theorem rows22250R_1906 : rowsJ2 83 84 46 47 ≤ 340745344574 := by decide +kernel

theorem rows22250R_1907 : rowsJ2 83 84 47 48 ≤ 459748072712 := by decide +kernel

theorem rows22250R_1908 : rowsJ2 83 84 48 49 ≤ 403090040726 := by decide +kernel

theorem rows22250R_1909 : rowsJ2 83 84 49 50 ≤ 347083175803 := by decide +kernel

theorem rows22250R_1910 : rowsJ2 83 84 50 51 ≤ 289793035063 := by decide +kernel

theorem rows22250R_1911 : rowsJ2 83 84 51 52 ≤ 233103001304 := by decide +kernel

theorem rows22250R_1912 : rowsJ2 83 84 52 53 ≤ 175031697192 := by decide +kernel

theorem rows22250R_1913 : rowsJ2 83 84 53 54 ≤ 117509763964 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1901
#print axioms SieveCert.rows22250R_1913
