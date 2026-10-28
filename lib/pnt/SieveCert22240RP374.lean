/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4840–4857 of 5066

File 374 of 387: the parts `rows22240R_4840` … `rows22240R_4857` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 97001 in units of a depth-4 test: row 177 columns 40–40, row 177
columns 41–41, row 177 columns 42–42, row 177 columns 43–43, row 177 columns 44–44, row 177 columns 45–45, row 177
columns 46–46, row 177 columns 47–47, row 177 columns 48–48, row 177 columns 49–49, row 177 columns 50–100, row 177
columns 101–339, row 178 columns 0–34, row 178 columns 35–36, row 178 columns 37–38, row 178 columns 39–39, row 178
columns 40–40, row 178 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4840 : rowsJ2 177 178 40 41 ≤ 17613187745767 := by decide +kernel

theorem rows22240R_4841 : rowsJ2 177 178 41 42 ≤ 19500915336824 := by decide +kernel

theorem rows22240R_4842 : rowsJ2 177 178 42 43 ≤ 21458831258646 := by decide +kernel

theorem rows22240R_4843 : rowsJ2 177 178 43 44 ≤ 23485042507995 := by decide +kernel

theorem rows22240R_4844 : rowsJ2 177 178 44 45 ≤ 25577964486728 := by decide +kernel

theorem rows22240R_4845 : rowsJ2 177 178 45 46 ≤ 25298847144151 := by decide +kernel

theorem rows22240R_4846 : rowsJ2 177 178 46 47 ≤ 22724506250411 := by decide +kernel

theorem rows22240R_4847 : rowsJ2 177 178 47 48 ≤ 20313000495316 := by decide +kernel

theorem rows22240R_4848 : rowsJ2 177 178 48 49 ≤ 18058520776007 := by decide +kernel

theorem rows22240R_4849 : rowsJ2 177 178 49 50 ≤ 15955714064760 := by decide +kernel

theorem rows22240R_4850 : rowsJ2 177 178 50 101 ≤ 486216324734040 := by decide +kernel

theorem rows22240R_4851 : rowsJ2 177 178 101 340 ≤ 2385128421909146 := by decide +kernel

theorem rows22240R_4852 : rowsJ2 178 179 0 35 ≤ 16449660847582 := by decide +kernel

theorem rows22240R_4853 : rowsJ2 178 179 35 37 ≤ 19122044220941 := by decide +kernel

theorem rows22240R_4854 : rowsJ2 178 179 37 39 ≤ 28802096021956 := by decide +kernel

theorem rows22240R_4855 : rowsJ2 178 179 39 40 ≤ 17086792562759 := by decide +kernel

theorem rows22240R_4856 : rowsJ2 178 179 40 41 ≤ 18978375655219 := by decide +kernel

theorem rows22240R_4857 : rowsJ2 178 179 41 42 ≤ 20942665198441 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4840
#print axioms SieveCert.rows22240R_4857
