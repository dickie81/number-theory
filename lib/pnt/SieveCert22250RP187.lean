/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1932–1940 of 5796

File 187 of 465: the parts `rows22250R_1932` … `rows22250R_1940` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 99495 tests: row 81 columns 49–49, row 81 columns 50–50, row 81 columns
51–51, row 81 columns 52–52, row 81 columns 53–53, row 81 columns 54–54, row 81 columns 55–55, row 81 columns 56–56,
row 81 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1932 : rowsJ2 81 82 49 50 ≤ 787984946441 := by decide +kernel

theorem rows22250R_1933 : rowsJ2 81 82 50 51 ≤ 1143803483094 := by decide +kernel

theorem rows22250R_1934 : rowsJ2 81 82 51 52 ≤ 1459482088506 := by decide +kernel

theorem rows22250R_1935 : rowsJ2 81 82 52 53 ≤ 1790123135494 := by decide +kernel

theorem rows22250R_1936 : rowsJ2 81 82 53 54 ≤ 1980297778140 := by decide +kernel

theorem rows22250R_1937 : rowsJ2 81 82 54 55 ≤ 1987119509462 := by decide +kernel

theorem rows22250R_1938 : rowsJ2 81 82 55 56 ≤ 1899858151274 := by decide +kernel

theorem rows22250R_1939 : rowsJ2 81 82 56 57 ≤ 1719938414270 := by decide +kernel

theorem rows22250R_1940 : rowsJ2 81 82 57 58 ≤ 1584643739888 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1932
#print axioms SieveCert.rows22250R_1940
