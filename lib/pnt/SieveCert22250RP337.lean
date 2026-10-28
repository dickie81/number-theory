/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4477–4494 of 4715

File 337 of 351: the parts `rows22250R_4477` … `rows22250R_4494` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, work 98463 in units of a depth-4 test: row 175 columns 46–46, row 175
columns 47–47, row 175 columns 48–48, row 175 columns 49–49, row 175 columns 50–51, row 175 columns 52–339, row 176
columns 0–34, row 176 columns 35–36, row 176 columns 37–38, row 176 columns 39–39, row 176 columns 40–40, row 176
columns 41–41, row 176 columns 42–42, row 176 columns 43–43, row 176 columns 44–44, row 176 columns 45–45, row 176
columns 46–46, row 176 columns 47–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_4477 : rowsJ2 175 176 46 47 ≤ 21047725055533 := by decide +kernel

theorem rows22250R_4478 : rowsJ2 175 176 47 48 ≤ 18766024058377 := by decide +kernel

theorem rows22250R_4479 : rowsJ2 175 176 48 49 ≤ 16635133836362 := by decide +kernel

theorem rows22250R_4480 : rowsJ2 175 176 49 50 ≤ 14650076624299 := by decide +kernel

theorem rows22250R_4481 : rowsJ2 175 176 50 52 ≤ 23905795027795 := by decide +kernel

theorem rows22250R_4482 : rowsJ2 175 176 52 340 ≤ 2838958027366277 := by decide +kernel

theorem rows22250R_4483 : rowsJ2 176 177 0 35 ≤ 16327438617796 := by decide +kernel

theorem rows22250R_4484 : rowsJ2 176 177 35 37 ≤ 18979147184483 := by decide +kernel

theorem rows22250R_4485 : rowsJ2 176 177 37 39 ≤ 26140241309986 := by decide +kernel

theorem rows22250R_4486 : rowsJ2 176 177 39 40 ≤ 15612776876942 := by decide +kernel

theorem rows22250R_4487 : rowsJ2 176 177 40 41 ≤ 17407781938301 := by decide +kernel

theorem rows22250R_4488 : rowsJ2 176 177 41 42 ≤ 19274458563158 := by decide +kernel

theorem rows22250R_4489 : rowsJ2 176 177 42 43 ≤ 21210603221821 := by decide +kernel

theorem rows22250R_4490 : rowsJ2 176 177 43 44 ≤ 23214327497285 := by decide +kernel

theorem rows22250R_4491 : rowsJ2 176 177 44 45 ≤ 25284045179997 := by decide +kernel

theorem rows22250R_4492 : rowsJ2 176 177 45 46 ≤ 22709844479147 := by decide +kernel

theorem rows22250R_4493 : rowsJ2 176 177 46 47 ≤ 20298634443874 := by decide +kernel

theorem rows22250R_4494 : rowsJ2 176 177 47 48 ≤ 18044594566920 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4477
#print axioms SieveCert.rows22250R_4494
