/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 886–901 of 4715

File 83 of 351: the parts `rows22250R_886` … `rows22250R_901` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 96464 in units of a depth-4 test: row 60 columns 31–31, row 60 columns
32–32, row 60 columns 33–33, row 60 columns 34–34, row 60 columns 35–35, row 60 columns 36–36, row 60 columns 37–37,
row 60 columns 38–38, row 60 columns 39–39, row 60 columns 40–40, row 60 columns 41–41, row 60 columns 42–42, row 60
columns 43–43, row 60 columns 44–44, row 60 columns 45–45, row 60 columns 46–46), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_886 : rowsJ2 60 61 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_887 : rowsJ2 60 61 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_888 : rowsJ2 60 61 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_889 : rowsJ2 60 61 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_890 : rowsJ2 60 61 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_891 : rowsJ2 60 61 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_892 : rowsJ2 60 61 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_893 : rowsJ2 60 61 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_894 : rowsJ2 60 61 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_895 : rowsJ2 60 61 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_896 : rowsJ2 60 61 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_897 : rowsJ2 60 61 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_898 : rowsJ2 60 61 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_899 : rowsJ2 60 61 44 45 ≤ 68937210631 := by decide +kernel

theorem rows22250R_900 : rowsJ2 60 61 45 46 ≤ 270578713529 := by decide +kernel

theorem rows22250R_901 : rowsJ2 60 61 46 47 ≤ 807230646983 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_886
#print axioms SieveCert.rows22250R_901
