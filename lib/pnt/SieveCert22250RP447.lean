/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5504–5519 of 5796

File 447 of 465: the parts `rows22250R_5504` … `rows22250R_5519` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98460 tests: row 185 columns 0–36, row 185 columns 37–38, row 185 columns
39–40, row 185 columns 41–41, row 185 columns 42–42, row 185 columns 43–43, row 185 columns 44–44, row 185 columns
45–45, row 185 columns 46–46, row 185 columns 47–47, row 185 columns 48–48, row 185 columns 49–49, row 185 columns
50–50, row 185 columns 51–51, row 185 columns 52–52, row 185 columns 53–53), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5504 : rowsJ2 185 186 0 37 ≤ 10894954178572 := by decide +kernel

theorem rows22250R_5505 : rowsJ2 185 186 37 39 ≤ 13479527619970 := by decide +kernel

theorem rows22250R_5506 : rowsJ2 185 186 39 41 ≤ 20599249340047 := by decide +kernel

theorem rows22250R_5507 : rowsJ2 185 186 41 42 ≤ 12316037367364 := by decide +kernel

theorem rows22250R_5508 : rowsJ2 185 186 42 43 ≤ 13740804010950 := by decide +kernel

theorem rows22250R_5509 : rowsJ2 185 186 43 44 ≤ 15223257553057 := by decide +kernel

theorem rows22250R_5510 : rowsJ2 185 186 44 45 ≤ 16761540075902 := by decide +kernel

theorem rows22250R_5511 : rowsJ2 185 186 45 46 ≤ 18354019861362 := by decide +kernel

theorem rows22250R_5512 : rowsJ2 185 186 46 47 ≤ 19999281559015 := by decide +kernel

theorem rows22250R_5513 : rowsJ2 185 186 47 48 ≤ 21696117689627 := by decide +kernel

theorem rows22250R_5514 : rowsJ2 185 186 48 49 ≤ 21474273144778 := by decide +kernel

theorem rows22250R_5515 : rowsJ2 185 186 49 50 ≤ 19392008200205 := by decide +kernel

theorem rows22250R_5516 : rowsJ2 185 186 50 51 ≤ 17434468208775 := by decide +kernel

theorem rows22250R_5517 : rowsJ2 185 186 51 52 ≤ 15597529725010 := by decide +kernel

theorem rows22250R_5518 : rowsJ2 185 186 52 53 ≤ 13877373374465 := by decide +kernel

theorem rows22250R_5519 : rowsJ2 185 186 53 54 ≤ 12270466540847 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5504
#print axioms SieveCert.rows22250R_5519
