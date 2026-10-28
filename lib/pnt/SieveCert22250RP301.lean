/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3930–3942 of 4715

File 301 of 351: the parts `rows22250R_3930` … `rows22250R_3942` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 95354 in units of a depth-4 test: row 148 columns 50–50, row 148
columns 51–51, row 148 columns 52–52, row 148 columns 53–53, row 148 columns 54–54, row 148 columns 55–55, row 148
columns 56–56, row 148 columns 57–57, row 148 columns 58–58, row 148 columns 59–59, row 148 columns 60–60, row 148
columns 61–61, row 148 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_3930 : rowsJ2 148 149 50 51 ≤ 6186039388074 := by decide +kernel

theorem rows22250R_3931 : rowsJ2 148 149 51 52 ≤ 7106388979887 := by decide +kernel

theorem rows22250R_3932 : rowsJ2 148 149 52 53 ≤ 8076386753637 := by decide +kernel

theorem rows22250R_3933 : rowsJ2 148 149 53 54 ≤ 9094085296262 := by decide +kernel

theorem rows22250R_3934 : rowsJ2 148 149 54 55 ≤ 10157703033941 := by decide +kernel

theorem rows22250R_3935 : rowsJ2 148 149 55 56 ≤ 11265615510872 := by decide +kernel

theorem rows22250R_3936 : rowsJ2 148 149 56 57 ≤ 12416347481338 := by decide +kernel

theorem rows22250R_3937 : rowsJ2 148 149 57 58 ≤ 13608565763488 := by decide +kernel

theorem rows22250R_3938 : rowsJ2 148 149 58 59 ≤ 14841072809347 := by decide +kernel

theorem rows22250R_3939 : rowsJ2 148 149 59 60 ≤ 13351878216900 := by decide +kernel

theorem rows22250R_3940 : rowsJ2 148 149 60 61 ≤ 11952324366943 := by decide +kernel

theorem rows22250R_3941 : rowsJ2 148 149 61 62 ≤ 10639934217853 := by decide +kernel

theorem rows22250R_3942 : rowsJ2 148 149 62 63 ≤ 9412403350010 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3930
#print axioms SieveCert.rows22250R_3942
