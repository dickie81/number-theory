/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2849–2865 of 5066

File 240 of 387: the parts `rows22240R_2849` … `rows22240R_2865` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 99618 in units of a depth-4 test: row 102 columns 17–27, row 102
columns 28–32, row 102 columns 33–34, row 102 columns 35–36, row 102 columns 37–37, row 102 columns 38–38, row 102
columns 39–39, row 102 columns 40–40, row 102 columns 41–41, row 102 columns 42–42, row 102 columns 43–43, row 102
columns 44–44, row 102 columns 45–45, row 102 columns 46–47, row 102 columns 48–49, row 102 columns 50–51, row 102
columns 52–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_2849 : rowsJ2 102 103 17 28 ≤ 0 := by decide +kernel

theorem rows22240R_2850 : rowsJ2 102 103 28 33 ≤ 5721346869244 := by decide +kernel

theorem rows22240R_2851 : rowsJ2 102 103 33 35 ≤ 9962690564543 := by decide +kernel

theorem rows22240R_2852 : rowsJ2 102 103 35 37 ≤ 17176104215866 := by decide +kernel

theorem rows22240R_2853 : rowsJ2 102 103 37 38 ≤ 11754668692784 := by decide +kernel

theorem rows22240R_2854 : rowsJ2 102 103 38 39 ≤ 13211360323448 := by decide +kernel

theorem rows22240R_2855 : rowsJ2 102 103 39 40 ≤ 14785813160783 := by decide +kernel

theorem rows22240R_2856 : rowsJ2 102 103 40 41 ≤ 16350676487145 := by decide +kernel

theorem rows22240R_2857 : rowsJ2 102 103 41 42 ≤ 14386839554961 := by decide +kernel

theorem rows22240R_2858 : rowsJ2 102 103 42 43 ≤ 12615169462859 := by decide +kernel

theorem rows22240R_2859 : rowsJ2 102 103 43 44 ≤ 10967863418050 := by decide +kernel

theorem rows22240R_2860 : rowsJ2 102 103 44 45 ≤ 9401472431698 := by decide +kernel

theorem rows22240R_2861 : rowsJ2 102 103 45 46 ≤ 7915916445032 := by decide +kernel

theorem rows22240R_2862 : rowsJ2 102 103 46 48 ≤ 11699017180935 := by decide +kernel

theorem rows22240R_2863 : rowsJ2 102 103 48 50 ≤ 7132808920529 := by decide +kernel

theorem rows22240R_2864 : rowsJ2 102 103 50 52 ≤ 3994229801196 := by decide +kernel

theorem rows22240R_2865 : rowsJ2 102 103 52 55 ≤ 2249080908077 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2849
#print axioms SieveCert.rows22240R_2865
