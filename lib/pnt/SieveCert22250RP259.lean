/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2846–2861 of 5796

File 259 of 465: the parts `rows22250R_2846` … `rows22250R_2861` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99475 tests: row 100 columns 40–40, row 100 columns 41–41, row 100 columns
42–42, row 100 columns 43–43, row 100 columns 44–44, row 100 columns 45–45, row 100 columns 46–46, row 100 columns
47–47, row 100 columns 48–48, row 100 columns 49–49, row 100 columns 50–50, row 100 columns 51–51, row 100 columns
52–52, row 100 columns 53–53, row 100 columns 54–54, row 100 columns 55–55), each a sum of refined costs (`rows2` or
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

theorem rows22250R_2846 : rowsJ2 100 101 40 41 ≤ 8462282172546 := by decide +kernel

theorem rows22250R_2847 : rowsJ2 100 101 41 42 ≤ 9619469987545 := by decide +kernel

theorem rows22250R_2848 : rowsJ2 100 101 42 43 ≤ 10870850201970 := by decide +kernel

theorem rows22250R_2849 : rowsJ2 100 101 43 44 ≤ 12212069315313 := by decide +kernel

theorem rows22250R_2850 : rowsJ2 100 101 44 45 ≤ 13545593886413 := by decide +kernel

theorem rows22250R_2851 : rowsJ2 100 101 45 46 ≤ 14645005676750 := by decide +kernel

theorem rows22250R_2852 : rowsJ2 100 101 46 47 ≤ 13072571675692 := by decide +kernel

theorem rows22250R_2853 : rowsJ2 100 101 47 48 ≤ 11517632143138 := by decide +kernel

theorem rows22250R_2854 : rowsJ2 100 101 48 49 ≤ 10108191857231 := by decide +kernel

theorem rows22250R_2855 : rowsJ2 100 101 49 50 ≤ 8792130412802 := by decide +kernel

theorem rows22250R_2856 : rowsJ2 100 101 50 51 ≤ 7614347429618 := by decide +kernel

theorem rows22250R_2857 : rowsJ2 100 101 51 52 ≤ 6522579327907 := by decide +kernel

theorem rows22250R_2858 : rowsJ2 100 101 52 53 ≤ 5490061952603 := by decide +kernel

theorem rows22250R_2859 : rowsJ2 100 101 53 54 ≤ 4517033457102 := by decide +kernel

theorem rows22250R_2860 : rowsJ2 100 101 54 55 ≤ 2893465246473 := by decide +kernel

theorem rows22250R_2861 : rowsJ2 100 101 55 56 ≤ 1519118290310 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2846
#print axioms SieveCert.rows22250R_2861
