/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1916–1931 of 5796

File 186 of 465: the parts `rows22250R_1916` … `rows22250R_1931` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94596 tests: row 81 columns 25–25, row 81 columns 26–26, row 81 columns
27–27, row 81 columns 28–29, row 81 columns 30–31, row 81 columns 32–33, row 81 columns 34–36, row 81 columns 37–39,
row 81 columns 40–41, row 81 columns 42–42, row 81 columns 43–43, row 81 columns 44–44, row 81 columns 45–45, row 81
columns 46–46, row 81 columns 47–47, row 81 columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1916 : rowsJ2 81 82 25 26 ≤ 1412120551 := by decide +kernel

theorem rows22250R_1917 : rowsJ2 81 82 26 27 ≤ 701999931 := by decide +kernel

theorem rows22250R_1918 : rowsJ2 81 82 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1919 : rowsJ2 81 82 28 30 ≤ 0 := by decide +kernel

theorem rows22250R_1920 : rowsJ2 81 82 30 32 ≤ 0 := by decide +kernel

theorem rows22250R_1921 : rowsJ2 81 82 32 34 ≤ 0 := by decide +kernel

theorem rows22250R_1922 : rowsJ2 81 82 34 37 ≤ 0 := by decide +kernel

theorem rows22250R_1923 : rowsJ2 81 82 37 40 ≤ 0 := by decide +kernel

theorem rows22250R_1924 : rowsJ2 81 82 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1925 : rowsJ2 81 82 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1926 : rowsJ2 81 82 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1927 : rowsJ2 81 82 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1928 : rowsJ2 81 82 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1929 : rowsJ2 81 82 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1930 : rowsJ2 81 82 47 48 ≤ 94417289560 := by decide +kernel

theorem rows22250R_1931 : rowsJ2 81 82 48 49 ≤ 423163085835 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1916
#print axioms SieveCert.rows22250R_1931
