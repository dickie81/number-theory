/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2131–2143 of 5066

File 187 of 387: the parts `rows22240R_2131` … `rows22240R_2143` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99447 in units of a depth-4 test: row 86 columns 42–42, row 86 columns
43–43, row 86 columns 44–44, row 86 columns 45–45, row 86 columns 46–46, row 86 columns 47–47, row 86 columns 48–48,
row 86 columns 49–49, row 86 columns 50–50, row 86 columns 51–51, row 86 columns 52–52, row 86 columns 53–53, row 86
columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_2131 : rowsJ2 86 87 42 43 ≤ 9580645026225 := by decide +kernel

theorem rows22240R_2132 : rowsJ2 86 87 43 44 ≤ 10968340368073 := by decide +kernel

theorem rows22240R_2133 : rowsJ2 86 87 44 45 ≤ 9670117072842 := by decide +kernel

theorem rows22240R_2134 : rowsJ2 86 87 45 46 ≤ 7261872231120 := by decide +kernel

theorem rows22240R_2135 : rowsJ2 86 87 46 47 ≤ 4153828940931 := by decide +kernel

theorem rows22240R_2136 : rowsJ2 86 87 47 48 ≤ 0 := by decide +kernel

theorem rows22240R_2137 : rowsJ2 86 87 48 49 ≤ 0 := by decide +kernel

theorem rows22240R_2138 : rowsJ2 86 87 49 50 ≤ 0 := by decide +kernel

theorem rows22240R_2139 : rowsJ2 86 87 50 51 ≤ 0 := by decide +kernel

theorem rows22240R_2140 : rowsJ2 86 87 51 52 ≤ 0 := by decide +kernel

theorem rows22240R_2141 : rowsJ2 86 87 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2142 : rowsJ2 86 87 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2143 : rowsJ2 86 87 54 55 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2131
#print axioms SieveCert.rows22240R_2143
