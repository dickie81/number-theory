/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 945–957 of 5796

File 100 of 465: the parts `rows22250R_945` … `rows22250R_957` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 93330 tests: row 61 columns 39–39, row 61 columns 40–40, row 61 columns
41–41, row 61 columns 42–42, row 61 columns 43–43, row 61 columns 44–44, row 61 columns 45–45, row 61 columns 46–46,
row 61 columns 47–47, row 61 columns 48–48, row 61 columns 49–49, row 61 columns 50–50, row 61 columns 51–51), each
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

theorem rows22250R_945 : rowsJ2 61 62 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_946 : rowsJ2 61 62 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_947 : rowsJ2 61 62 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_948 : rowsJ2 61 62 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_949 : rowsJ2 61 62 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_950 : rowsJ2 61 62 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_951 : rowsJ2 61 62 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_952 : rowsJ2 61 62 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_953 : rowsJ2 61 62 47 48 ≤ 111460314916 := by decide +kernel

theorem rows22250R_954 : rowsJ2 61 62 48 49 ≤ 499547180692 := by decide +kernel

theorem rows22250R_955 : rowsJ2 61 62 49 50 ≤ 930222109629 := by decide +kernel

theorem rows22250R_956 : rowsJ2 61 62 50 51 ≤ 1399081551200 := by decide +kernel

theorem rows22250R_957 : rowsJ2 61 62 51 52 ≤ 2013973286641 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_945
#print axioms SieveCert.rows22250R_957
