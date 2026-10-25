/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2963–2974 of 5796

File 268 of 465: the parts `rows22250R_2963` … `rows22250R_2974` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99888 tests: row 102 columns 68–73, row 102 columns 74–78, row 102 columns
79–81, row 102 columns 82–83, row 102 columns 84–84, row 102 columns 85–85, row 102 columns 86–86, row 102 columns
87–87, row 102 columns 88–88, row 102 columns 89–89, row 102 columns 90–90, row 102 columns 91–91), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2963 : rowsJ2 102 103 68 74 ≤ 0 := by decide +kernel

theorem rows22250R_2964 : rowsJ2 102 103 74 79 ≤ 0 := by decide +kernel

theorem rows22250R_2965 : rowsJ2 102 103 79 82 ≤ 202116635043 := by decide +kernel

theorem rows22250R_2966 : rowsJ2 102 103 82 84 ≤ 841308284093 := by decide +kernel

theorem rows22250R_2967 : rowsJ2 102 103 84 85 ≤ 799608874958 := by decide +kernel

theorem rows22250R_2968 : rowsJ2 102 103 85 86 ≤ 1119169970567 := by decide +kernel

theorem rows22250R_2969 : rowsJ2 102 103 86 87 ≤ 1498811497381 := by decide +kernel

theorem rows22250R_2970 : rowsJ2 102 103 87 88 ≤ 1997932403025 := by decide +kernel

theorem rows22250R_2971 : rowsJ2 102 103 88 89 ≤ 2563429488427 := by decide +kernel

theorem rows22250R_2972 : rowsJ2 102 103 89 90 ≤ 2949126648846 := by decide +kernel

theorem rows22250R_2973 : rowsJ2 102 103 90 91 ≤ 2785565141891 := by decide +kernel

theorem rows22250R_2974 : rowsJ2 102 103 91 92 ≤ 2619248262726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2963
#print axioms SieveCert.rows22250R_2974
