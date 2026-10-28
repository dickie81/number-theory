/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4925–4940 of 5066

File 379 of 387: the parts `rows22240R_4925` … `rows22240R_4940` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 93605 in units of a depth-4 test: row 183 columns 42–42, row 183
columns 43–43, row 183 columns 44–44, row 183 columns 45–339, row 184 columns 0–32, row 184 columns 33–35, row 184
columns 36–37, row 184 columns 38–38, row 184 columns 39–39, row 184 columns 40–40, row 184 columns 41–41, row 184
columns 42–42, row 184 columns 43–43, row 184 columns 44–339, row 185 columns 0–32, row 185 columns 33–34), each a
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

theorem rows22240R_4925 : rowsJ2 183 184 42 43 ≤ 28906374088882 := by decide +kernel

theorem rows22240R_4926 : rowsJ2 183 184 43 44 ≤ 25952610932844 := by decide +kernel

theorem rows22240R_4927 : rowsJ2 183 184 44 45 ≤ 23188375956227 := by decide +kernel

theorem rows22240R_4928 : rowsJ2 183 184 45 340 ≤ 3540100115148752 := by decide +kernel

theorem rows22240R_4929 : rowsJ2 184 185 0 33 ≤ 17845999588969 := by decide +kernel

theorem rows22240R_4930 : rowsJ2 184 185 33 36 ≤ 35438924559568 := by decide +kernel

theorem rows22240R_4931 : rowsJ2 184 185 36 38 ≤ 39754214175678 := by decide +kernel

theorem rows22240R_4932 : rowsJ2 184 185 38 39 ≤ 23985723183013 := by decide +kernel

theorem rows22240R_4933 : rowsJ2 184 185 39 40 ≤ 26307679422164 := by decide +kernel

theorem rows22240R_4934 : rowsJ2 184 185 40 41 ≤ 28708042069934 := by decide +kernel

theorem rows22240R_4935 : rowsJ2 184 185 41 42 ≤ 31185387132013 := by decide +kernel

theorem rows22240R_4936 : rowsJ2 184 185 42 43 ≤ 28060286701621 := by decide +kernel

theorem rows22240R_4937 : rowsJ2 184 185 43 44 ≤ 25133734251353 := by decide +kernel

theorem rows22240R_4938 : rowsJ2 184 185 44 340 ≤ 3677592091602928 := by decide +kernel

theorem rows22240R_4939 : rowsJ2 185 186 0 33 ≤ 20910033336678 := by decide +kernel

theorem rows22240R_4940 : rowsJ2 185 186 33 35 ≤ 22864540934856 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4925
#print axioms SieveCert.rows22240R_4940
