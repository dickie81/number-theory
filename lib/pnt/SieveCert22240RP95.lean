/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 957–970 of 5066

File 95 of 387: the parts `rows22240R_957` … `rows22240R_970` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 92953 in units of a depth-4 test: row 61 columns 37–37, row 61 columns
38–38, row 61 columns 39–39, row 61 columns 40–40, row 61 columns 41–41, row 61 columns 42–42, row 61 columns 43–43,
row 61 columns 44–44, row 61 columns 45–45, row 61 columns 46–46, row 61 columns 47–47, row 61 columns 48–48, row 61
columns 49–49, row 61 columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_957 : rowsJ2 61 62 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_958 : rowsJ2 61 62 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_959 : rowsJ2 61 62 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_960 : rowsJ2 61 62 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_961 : rowsJ2 61 62 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_962 : rowsJ2 61 62 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_963 : rowsJ2 61 62 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_964 : rowsJ2 61 62 44 45 ≤ 69313109741 := by decide +kernel

theorem rows22240R_965 : rowsJ2 61 62 45 46 ≤ 202702177217 := by decide +kernel

theorem rows22240R_966 : rowsJ2 61 62 46 47 ≤ 395297651368 := by decide +kernel

theorem rows22240R_967 : rowsJ2 61 62 47 48 ≤ 843993365497 := by decide +kernel

theorem rows22240R_968 : rowsJ2 61 62 48 49 ≤ 1612449117569 := by decide +kernel

theorem rows22240R_969 : rowsJ2 61 62 49 50 ≤ 2486608159061 := by decide +kernel

theorem rows22240R_970 : rowsJ2 61 62 50 51 ≤ 3392958079892 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_957
#print axioms SieveCert.rows22240R_970
