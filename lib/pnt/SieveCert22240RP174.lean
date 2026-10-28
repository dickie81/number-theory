/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1946–1959 of 5066

File 174 of 387: the parts `rows22240R_1946` … `rows22240R_1959` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98060 in units of a depth-4 test: row 82 columns 31–33, row 82 columns
34–36, row 82 columns 37–38, row 82 columns 39–40, row 82 columns 41–41, row 82 columns 42–42, row 82 columns 43–43,
row 82 columns 44–44, row 82 columns 45–45, row 82 columns 46–46, row 82 columns 47–47, row 82 columns 48–48, row 82
columns 49–49, row 82 columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_1946 : rowsJ2 82 83 31 34 ≤ 97312380773 := by decide +kernel

theorem rows22240R_1947 : rowsJ2 82 83 34 37 ≤ 2880868732850 := by decide +kernel

theorem rows22240R_1948 : rowsJ2 82 83 37 39 ≤ 5790875583937 := by decide +kernel

theorem rows22240R_1949 : rowsJ2 82 83 39 41 ≤ 8550447910940 := by decide +kernel

theorem rows22240R_1950 : rowsJ2 82 83 41 42 ≤ 3315049045596 := by decide +kernel

theorem rows22240R_1951 : rowsJ2 82 83 42 43 ≤ 2109548253638 := by decide +kernel

theorem rows22240R_1952 : rowsJ2 82 83 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1953 : rowsJ2 82 83 44 45 ≤ 57998000609 := by decide +kernel

theorem rows22240R_1954 : rowsJ2 82 83 45 46 ≤ 169611795541 := by decide +kernel

theorem rows22240R_1955 : rowsJ2 82 83 46 47 ≤ 330766769959 := by decide +kernel

theorem rows22240R_1956 : rowsJ2 82 83 47 48 ≤ 497535548568 := by decide +kernel

theorem rows22240R_1957 : rowsJ2 82 83 48 49 ≤ 726609529759 := by decide +kernel

theorem rows22240R_1958 : rowsJ2 82 83 49 50 ≤ 788417497108 := by decide +kernel

theorem rows22240R_1959 : rowsJ2 82 83 50 51 ≤ 733750643729 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1946
#print axioms SieveCert.rows22240R_1959
