/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1931–1945 of 5066

File 173 of 387: the parts `rows22240R_1931` … `rows22240R_1945` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99311 in units of a depth-4 test: row 81 columns 67–68, row 81 columns
69–70, row 81 columns 71–72, row 81 columns 73–75, row 81 columns 76–77, row 81 columns 78–79, row 81 columns 80–80,
row 81 columns 81–339, row 82 columns 0–17, row 82 columns 18–19, row 82 columns 20–21, row 82 columns 22–23, row 82
columns 24–25, row 82 columns 26–27, row 82 columns 28–30), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_1931 : rowsJ2 81 82 67 69 ≤ 0 := by decide +kernel

theorem rows22240R_1932 : rowsJ2 81 82 69 71 ≤ 0 := by decide +kernel

theorem rows22240R_1933 : rowsJ2 81 82 71 73 ≤ 0 := by decide +kernel

theorem rows22240R_1934 : rowsJ2 81 82 73 76 ≤ 0 := by decide +kernel

theorem rows22240R_1935 : rowsJ2 81 82 76 78 ≤ 1134079445366 := by decide +kernel

theorem rows22240R_1936 : rowsJ2 81 82 78 80 ≤ 4319107130357 := by decide +kernel

theorem rows22240R_1937 : rowsJ2 81 82 80 81 ≤ 2760449275749 := by decide +kernel

theorem rows22240R_1938 : rowsJ2 81 82 81 340 ≤ 2831251593723 := by decide +kernel

theorem rows22240R_1939 : rowsJ2 82 83 0 18 ≤ 205453503663 := by decide +kernel

theorem rows22240R_1940 : rowsJ2 82 83 18 20 ≤ 16893940589 := by decide +kernel

theorem rows22240R_1941 : rowsJ2 82 83 20 22 ≤ 10390751325 := by decide +kernel

theorem rows22240R_1942 : rowsJ2 82 83 22 24 ≤ 1887392822 := by decide +kernel

theorem rows22240R_1943 : rowsJ2 82 83 24 26 ≤ 0 := by decide +kernel

theorem rows22240R_1944 : rowsJ2 82 83 26 28 ≤ 0 := by decide +kernel

theorem rows22240R_1945 : rowsJ2 82 83 28 31 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1931
#print axioms SieveCert.rows22240R_1945
