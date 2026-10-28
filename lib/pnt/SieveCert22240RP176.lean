/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1974–1988 of 5066

File 176 of 387: the parts `rows22240R_1974` … `rows22240R_1988` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97971 in units of a depth-4 test: row 82 columns 65–65, row 82 columns
66–67, row 82 columns 68–69, row 82 columns 70–71, row 82 columns 72–74, row 82 columns 75–77, row 82 columns 78–79,
row 82 columns 80–80, row 82 columns 81–81, row 82 columns 82–339, row 83 columns 0–16, row 83 columns 17–19, row 83
columns 20–21, row 83 columns 22–23, row 83 columns 24–25), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1974 : rowsJ2 82 83 65 66 ≤ 0 := by decide +kernel

theorem rows22240R_1975 : rowsJ2 82 83 66 68 ≤ 0 := by decide +kernel

theorem rows22240R_1976 : rowsJ2 82 83 68 70 ≤ 0 := by decide +kernel

theorem rows22240R_1977 : rowsJ2 82 83 70 72 ≤ 0 := by decide +kernel

theorem rows22240R_1978 : rowsJ2 82 83 72 75 ≤ 0 := by decide +kernel

theorem rows22240R_1979 : rowsJ2 82 83 75 78 ≤ 1137415373415 := by decide +kernel

theorem rows22240R_1980 : rowsJ2 82 83 78 80 ≤ 3806847337732 := by decide +kernel

theorem rows22240R_1981 : rowsJ2 82 83 80 81 ≤ 2328015036403 := by decide +kernel

theorem rows22240R_1982 : rowsJ2 82 83 81 82 ≤ 2497152108178 := by decide +kernel

theorem rows22240R_1983 : rowsJ2 82 83 82 340 ≤ 2794186255946 := by decide +kernel

theorem rows22240R_1984 : rowsJ2 83 84 0 17 ≤ 155269581547 := by decide +kernel

theorem rows22240R_1985 : rowsJ2 83 84 17 20 ≤ 17026618494 := by decide +kernel

theorem rows22240R_1986 : rowsJ2 83 84 20 22 ≤ 5728298717 := by decide +kernel

theorem rows22240R_1987 : rowsJ2 83 84 22 24 ≤ 0 := by decide +kernel

theorem rows22240R_1988 : rowsJ2 83 84 24 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1974
#print axioms SieveCert.rows22240R_1988
