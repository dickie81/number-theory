/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4711–4726 of 5066

File 366 of 387: the parts `rows22240R_4711` … `rows22240R_4726` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94665 in units of a depth-4 test: row 169 columns 49–49, row 169
columns 50–50, row 169 columns 51–51, row 169 columns 52–52, row 169 columns 53–53, row 169 columns 54–54, row 169
columns 55–56, row 169 columns 57–58, row 169 columns 59–339, row 170 columns 0–37, row 170 columns 38–39, row 170
columns 40–41, row 170 columns 42–42, row 170 columns 43–43, row 170 columns 44–44, row 170 columns 45–45), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_4711 : rowsJ2 169 170 49 50 ≤ 21413574452291 := by decide +kernel

theorem rows22240R_4712 : rowsJ2 169 170 50 51 ≤ 19245046091119 := by decide +kernel

theorem rows22240R_4713 : rowsJ2 169 170 51 52 ≤ 17211452527906 := by decide +kernel

theorem rows22240R_4714 : rowsJ2 169 170 52 53 ≤ 15308336669676 := by decide +kernel

theorem rows22240R_4715 : rowsJ2 169 170 53 54 ≤ 13531563726471 := by decide +kernel

theorem rows22240R_4716 : rowsJ2 169 170 54 55 ≤ 11877310607092 := by decide +kernel

theorem rows22240R_4717 : rowsJ2 169 170 55 57 ≤ 19264744608209 := by decide +kernel

theorem rows22240R_4718 : rowsJ2 169 170 57 59 ≤ 14035931449681 := by decide +kernel

theorem rows22240R_4719 : rowsJ2 169 170 59 340 ≤ 2658448629464660 := by decide +kernel

theorem rows22240R_4720 : rowsJ2 170 171 0 38 ≤ 17144388241835 := by decide +kernel

theorem rows22240R_4721 : rowsJ2 170 171 38 40 ≤ 16071135551735 := by decide +kernel

theorem rows22240R_4722 : rowsJ2 170 171 40 42 ≤ 21386357041884 := by decide +kernel

theorem rows22240R_4723 : rowsJ2 170 171 42 43 ≤ 12866078533645 := by decide +kernel

theorem rows22240R_4724 : rowsJ2 170 171 43 44 ≤ 14404703387402 := by decide +kernel

theorem rows22240R_4725 : rowsJ2 170 171 44 45 ≤ 16007743636437 := by decide +kernel

theorem rows22240R_4726 : rowsJ2 170 171 45 46 ≤ 17673053128178 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4711
#print axioms SieveCert.rows22240R_4726
