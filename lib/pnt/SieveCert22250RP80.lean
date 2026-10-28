/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 851–865 of 4715

File 80 of 351: the parts `rows22250R_851` … `rows22250R_865` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 92316 in units of a depth-4 test: row 59 columns 36–36, row 59 columns
37–37, row 59 columns 38–38, row 59 columns 39–39, row 59 columns 40–40, row 59 columns 41–41, row 59 columns 42–42,
row 59 columns 43–43, row 59 columns 44–44, row 59 columns 45–45, row 59 columns 46–46, row 59 columns 47–47, row 59
columns 48–48, row 59 columns 49–49, row 59 columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_851 : rowsJ2 59 60 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_852 : rowsJ2 59 60 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_853 : rowsJ2 59 60 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_854 : rowsJ2 59 60 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_855 : rowsJ2 59 60 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_856 : rowsJ2 59 60 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_857 : rowsJ2 59 60 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_858 : rowsJ2 59 60 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_859 : rowsJ2 59 60 44 45 ≤ 69587364503 := by decide +kernel

theorem rows22250R_860 : rowsJ2 59 60 45 46 ≤ 273130569005 := by decide +kernel

theorem rows22250R_861 : rowsJ2 59 60 46 47 ≤ 814843721641 := by decide +kernel

theorem rows22250R_862 : rowsJ2 59 60 47 48 ≤ 1618153235686 := by decide +kernel

theorem rows22250R_863 : rowsJ2 59 60 48 49 ≤ 2391063671241 := by decide +kernel

theorem rows22250R_864 : rowsJ2 59 60 49 50 ≤ 3270488843703 := by decide +kernel

theorem rows22250R_865 : rowsJ2 59 60 50 51 ≤ 4393472329336 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_851
#print axioms SieveCert.rows22250R_865
