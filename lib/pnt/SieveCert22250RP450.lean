/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5552–5567 of 5796

File 450 of 465: the parts `rows22250R_5552` … `rows22250R_5567` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95156 tests: row 187 columns 51–51, row 187 columns 52–52, row 187 columns
53–359, row 188 columns 0–35, row 188 columns 36–37, row 188 columns 38–39, row 188 columns 40–40, row 188 columns
41–41, row 188 columns 42–42, row 188 columns 43–43, row 188 columns 44–44, row 188 columns 45–45, row 188 columns
46–46, row 188 columns 47–47, row 188 columns 48–48, row 188 columns 49–49), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5552 : rowsJ2 187 188 51 52 ≤ 14444214017241 := by decide +kernel

theorem rows22250R_5553 : rowsJ2 187 188 52 53 ≤ 12770480507753 := by decide +kernel

theorem rows22250R_5554 : rowsJ2 187 188 53 360 ≤ 2748769223295862 := by decide +kernel

theorem rows22250R_5555 : rowsJ2 188 189 0 36 ≤ 11307522354490 := by decide +kernel

theorem rows22250R_5556 : rowsJ2 188 189 36 38 ≤ 13990848114438 := by decide +kernel

theorem rows22250R_5557 : rowsJ2 188 189 38 40 ≤ 22403007595085 := by decide +kernel

theorem rows22250R_5558 : rowsJ2 188 189 40 41 ≤ 13869608110501 := by decide +kernel

theorem rows22250R_5559 : rowsJ2 188 189 41 42 ≤ 15413418428098 := by decide +kernel

theorem rows22250R_5560 : rowsJ2 188 189 42 43 ≤ 17017224137095 := by decide +kernel

theorem rows22250R_5561 : rowsJ2 188 189 43 44 ≤ 18679208839992 := by decide +kernel

theorem rows22250R_5562 : rowsJ2 188 189 44 45 ≤ 20397798359800 := by decide +kernel

theorem rows22250R_5563 : rowsJ2 188 189 45 46 ≤ 22171650898841 := by decide +kernel

theorem rows22250R_5564 : rowsJ2 188 189 46 47 ≤ 23999648685272 := by decide +kernel

theorem rows22250R_5565 : rowsJ2 188 189 47 48 ≤ 21713552990785 := by decide +kernel

theorem rows22250R_5566 : rowsJ2 188 189 48 49 ≤ 19563521857831 := by decide +kernel

theorem rows22250R_5567 : rowsJ2 188 189 49 50 ≤ 17544829501545 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5552
#print axioms SieveCert.rows22250R_5567
