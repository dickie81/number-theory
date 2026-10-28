/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 815–828 of 4715

File 77 of 351: the parts `rows22250R_815` … `rows22250R_828` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 94365 in units of a depth-4 test: row 58 columns 39–39, row 58 columns
40–40, row 58 columns 41–41, row 58 columns 42–42, row 58 columns 43–43, row 58 columns 44–44, row 58 columns 45–45,
row 58 columns 46–46, row 58 columns 47–47, row 58 columns 48–48, row 58 columns 49–49, row 58 columns 50–50, row 58
columns 51–51, row 58 columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_815 : rowsJ2 58 59 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_816 : rowsJ2 58 59 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_817 : rowsJ2 58 59 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_818 : rowsJ2 58 59 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_819 : rowsJ2 58 59 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_820 : rowsJ2 58 59 44 45 ≤ 70249898469 := by decide +kernel

theorem rows22250R_821 : rowsJ2 58 59 45 46 ≤ 275731016376 := by decide +kernel

theorem rows22250R_822 : rowsJ2 58 59 46 47 ≤ 822601762864 := by decide +kernel

theorem rows22250R_823 : rowsJ2 58 59 47 48 ≤ 1633559502158 := by decide +kernel

theorem rows22250R_824 : rowsJ2 58 59 48 49 ≤ 2413828736536 := by decide +kernel

theorem rows22250R_825 : rowsJ2 58 59 49 50 ≤ 3301626823411 := by decide +kernel

theorem rows22250R_826 : rowsJ2 58 59 50 51 ≤ 4435302116488 := by decide +kernel

theorem rows22250R_827 : rowsJ2 58 59 51 52 ≤ 5811243686379 := by decide +kernel

theorem rows22250R_828 : rowsJ2 58 59 52 53 ≤ 7132117698924 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_815
#print axioms SieveCert.rows22250R_828
