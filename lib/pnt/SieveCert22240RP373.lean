/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4823–4839 of 5066

File 373 of 387: the parts `rows22240R_4823` … `rows22240R_4839` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 98196 in units of a depth-4 test: row 176 columns 38–39, row 176
columns 40–40, row 176 columns 41–41, row 176 columns 42–42, row 176 columns 43–43, row 176 columns 44–44, row 176
columns 45–45, row 176 columns 46–46, row 176 columns 47–47, row 176 columns 48–48, row 176 columns 49–49, row 176
columns 50–50, row 176 columns 51–108, row 176 columns 109–339, row 177 columns 0–35, row 177 columns 36–37, row 177
columns 38–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_4823 : rowsJ2 176 177 38 40 ≤ 27560490362923 := by decide +kernel

theorem rows22240R_4824 : rowsJ2 176 177 40 41 ≤ 16353763927727 := by decide +kernel

theorem rows22240R_4825 : rowsJ2 176 177 41 42 ≤ 18166607084996 := by decide +kernel

theorem rows22240R_4826 : rowsJ2 176 177 42 43 ≤ 20049306275769 := by decide +kernel

theorem rows22240R_4827 : rowsJ2 176 177 43 44 ≤ 21999833310536 := by decide +kernel

theorem rows22240R_4828 : rowsJ2 176 177 44 45 ≤ 24016464621409 := by decide +kernel

theorem rows22240R_4829 : rowsJ2 176 177 45 46 ≤ 26097776250232 := by decide +kernel

theorem rows22240R_4830 : rowsJ2 176 177 46 47 ≤ 23497967623405 := by decide +kernel

theorem rows22240R_4831 : rowsJ2 176 177 47 48 ≤ 21060058836399 := by decide +kernel

theorem rows22240R_4832 : rowsJ2 176 177 48 49 ≤ 18778201085255 := by decide +kernel

theorem rows22240R_4833 : rowsJ2 176 177 49 50 ≤ 16647005185310 := by decide +kernel

theorem rows22240R_4834 : rowsJ2 176 177 50 51 ≤ 14661506781839 := by decide +kernel

theorem rows22240R_4835 : rowsJ2 176 177 51 109 ≤ 1036514764534234 := by decide +kernel

theorem rows22240R_4836 : rowsJ2 176 177 109 340 ≤ 1802104575823337 := by decide +kernel

theorem rows22240R_4837 : rowsJ2 177 178 0 36 ≤ 21481893069506 := by decide +kernel

theorem rows22240R_4838 : rowsJ2 177 178 36 38 ≤ 22203941029738 := by decide +kernel

theorem rows22240R_4839 : rowsJ2 177 178 38 40 ≤ 29855355303071 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4823
#print axioms SieveCert.rows22240R_4839
