/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2756–2770 of 5066

File 234 of 387: the parts `rows22240R_2756` … `rows22240R_2770` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 92241 in units of a depth-4 test: row 100 columns 0–16, row 100 columns
17–25, row 100 columns 26–32, row 100 columns 33–35, row 100 columns 36–37, row 100 columns 38–38, row 100 columns
39–39, row 100 columns 40–40, row 100 columns 41–41, row 100 columns 42–42, row 100 columns 43–43, row 100 columns
44–44, row 100 columns 45–45, row 100 columns 46–46, row 100 columns 47–47), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2756 : rowsJ2 100 101 0 17 ≤ 0 := by decide +kernel

theorem rows22240R_2757 : rowsJ2 100 101 17 26 ≤ 0 := by decide +kernel

theorem rows22240R_2758 : rowsJ2 100 101 26 33 ≤ 4161952542839 := by decide +kernel

theorem rows22240R_2759 : rowsJ2 100 101 33 36 ≤ 14769210862844 := by decide +kernel

theorem rows22240R_2760 : rowsJ2 100 101 36 38 ≤ 18908436490597 := by decide +kernel

theorem rows22240R_2761 : rowsJ2 100 101 38 39 ≤ 12071707948238 := by decide +kernel

theorem rows22240R_2762 : rowsJ2 100 101 39 40 ≤ 13574372738703 := by decide +kernel

theorem rows22240R_2763 : rowsJ2 100 101 40 41 ≤ 15084542971217 := by decide +kernel

theorem rows22240R_2764 : rowsJ2 100 101 41 42 ≤ 16464442262373 := by decide +kernel

theorem rows22240R_2765 : rowsJ2 100 101 42 43 ≤ 14623641850512 := by decide +kernel

theorem rows22240R_2766 : rowsJ2 100 101 43 44 ≤ 12907640822171 := by decide +kernel

theorem rows22240R_2767 : rowsJ2 100 101 44 45 ≤ 11272596887694 := by decide +kernel

theorem rows22240R_2768 : rowsJ2 100 101 45 46 ≤ 9655794588500 := by decide +kernel

theorem rows22240R_2769 : rowsJ2 100 101 46 47 ≤ 8118096543451 := by decide +kernel

theorem rows22240R_2770 : rowsJ2 100 101 47 48 ≤ 6659516713447 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2756
#print axioms SieveCert.rows22240R_2770
