/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2934–2947 of 5796

File 266 of 465: the parts `rows22250R_2934` … `rows22250R_2947` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93437 tests: row 101 columns 99–99, row 101 columns 100–100, row 101 columns
101–359, row 102 columns 0–15, row 102 columns 16–21, row 102 columns 22–30, row 102 columns 31–34, row 102 columns
35–36, row 102 columns 37–38, row 102 columns 39–39, row 102 columns 40–40, row 102 columns 41–41, row 102 columns
42–42, row 102 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2934 : rowsJ2 101 102 99 100 ≤ 3491661874815 := by decide +kernel

theorem rows22250R_2935 : rowsJ2 101 102 100 101 ≤ 3845324130996 := by decide +kernel

theorem rows22250R_2936 : rowsJ2 101 102 101 360 ≤ 4232886861486 := by decide +kernel

theorem rows22250R_2937 : rowsJ2 102 103 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2938 : rowsJ2 102 103 16 22 ≤ 0 := by decide +kernel

theorem rows22250R_2939 : rowsJ2 102 103 22 31 ≤ 0 := by decide +kernel

theorem rows22250R_2940 : rowsJ2 102 103 31 35 ≤ 3721031894610 := by decide +kernel

theorem rows22250R_2941 : rowsJ2 102 103 35 37 ≤ 6619436369270 := by decide +kernel

theorem rows22250R_2942 : rowsJ2 102 103 37 39 ≤ 11901887383973 := by decide +kernel

theorem rows22250R_2943 : rowsJ2 102 103 39 40 ≤ 8069615717143 := by decide +kernel

theorem rows22250R_2944 : rowsJ2 102 103 40 41 ≤ 9273158173452 := by decide +kernel

theorem rows22250R_2945 : rowsJ2 102 103 41 42 ≤ 10573624954608 := by decide +kernel

theorem rows22250R_2946 : rowsJ2 102 103 42 43 ≤ 11966501017363 := by decide +kernel

theorem rows22250R_2947 : rowsJ2 102 103 43 44 ≤ 13313282059200 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2934
#print axioms SieveCert.rows22250R_2947
