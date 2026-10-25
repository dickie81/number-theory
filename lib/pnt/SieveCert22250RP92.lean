/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 863–873 of 5796

File 92 of 465: the parts `rows22250R_863` … `rows22250R_873` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95034 tests: row 59 columns 36–36, row 59 columns 37–37, row 59 columns
38–38, row 59 columns 39–39, row 59 columns 40–40, row 59 columns 41–41, row 59 columns 42–42, row 59 columns 43–43,
row 59 columns 44–44, row 59 columns 45–45, row 59 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_863 : rowsJ2 59 60 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_864 : rowsJ2 59 60 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_865 : rowsJ2 59 60 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_866 : rowsJ2 59 60 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_867 : rowsJ2 59 60 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_868 : rowsJ2 59 60 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_869 : rowsJ2 59 60 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_870 : rowsJ2 59 60 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_871 : rowsJ2 59 60 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_872 : rowsJ2 59 60 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_873 : rowsJ2 59 60 46 47 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_863
#print axioms SieveCert.rows22250R_873
