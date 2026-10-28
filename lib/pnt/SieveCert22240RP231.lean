/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2711–2726 of 5066

File 231 of 387: the parts `rows22240R_2711` … `rows22240R_2726` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 98542 in units of a depth-4 test: row 99 columns 0–16, row 99 columns
17–24, row 99 columns 25–32, row 99 columns 33–35, row 99 columns 36–37, row 99 columns 38–38, row 99 columns 39–39,
row 99 columns 40–40, row 99 columns 41–41, row 99 columns 42–42, row 99 columns 43–43, row 99 columns 44–44, row 99
columns 45–45, row 99 columns 46–46, row 99 columns 47–47, row 99 columns 48–48), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2711 : rowsJ2 99 100 0 17 ≤ 0 := by decide +kernel

theorem rows22240R_2712 : rowsJ2 99 100 17 25 ≤ 0 := by decide +kernel

theorem rows22240R_2713 : rowsJ2 99 100 25 33 ≤ 3652759599358 := by decide +kernel

theorem rows22240R_2714 : rowsJ2 99 100 33 36 ≤ 13464347480289 := by decide +kernel

theorem rows22240R_2715 : rowsJ2 99 100 36 38 ≤ 17616683906639 := by decide +kernel

theorem rows22240R_2716 : rowsJ2 99 100 38 39 ≤ 11396260423932 := by decide +kernel

theorem rows22240R_2717 : rowsJ2 99 100 39 40 ≤ 12918097899848 := by decide +kernel

theorem rows22240R_2718 : rowsJ2 99 100 40 41 ≤ 14447287930213 := by decide +kernel

theorem rows22240R_2719 : rowsJ2 99 100 41 42 ≤ 15862677018169 := by decide +kernel

theorem rows22240R_2720 : rowsJ2 99 100 42 43 ≤ 15563050475469 := by decide +kernel

theorem rows22240R_2721 : rowsJ2 99 100 43 44 ≤ 13843755916145 := by decide +kernel

theorem rows22240R_2722 : rowsJ2 99 100 44 45 ≤ 12144747030940 := by decide +kernel

theorem rows22240R_2723 : rowsJ2 99 100 45 46 ≤ 10525733569251 := by decide +kernel

theorem rows22240R_2724 : rowsJ2 99 100 46 47 ≤ 8924300240232 := by decide +kernel

theorem rows22240R_2725 : rowsJ2 99 100 47 48 ≤ 7401098331790 := by decide +kernel

theorem rows22240R_2726 : rowsJ2 99 100 48 49 ≤ 6055738706801 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2711
#print axioms SieveCert.rows22240R_2726
