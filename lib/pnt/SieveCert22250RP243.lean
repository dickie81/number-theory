/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3093–3107 of 4715

File 243 of 351: the parts `rows22250R_3093` … `rows22250R_3107` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 99446 in units of a depth-4 test: row 115 columns 75–77, row 115
columns 78–80, row 115 columns 81–83, row 115 columns 84–86, row 115 columns 87–89, row 115 columns 90–91, row 115
columns 92–93, row 115 columns 94–95, row 115 columns 96–339, row 116 columns 0–26, row 116 columns 27–29, row 116
columns 30–31, row 116 columns 32–33, row 116 columns 34–36, row 116 columns 37–40), each a sum of refined costs
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

theorem rows22250R_3093 : rowsJ2 115 116 75 78 ≤ 0 := by decide +kernel

theorem rows22250R_3094 : rowsJ2 115 116 78 81 ≤ 0 := by decide +kernel

theorem rows22250R_3095 : rowsJ2 115 116 81 84 ≤ 811507110190 := by decide +kernel

theorem rows22250R_3096 : rowsJ2 115 116 84 87 ≤ 4444838224994 := by decide +kernel

theorem rows22250R_3097 : rowsJ2 115 116 87 90 ≤ 10365042305443 := by decide +kernel

theorem rows22250R_3098 : rowsJ2 115 116 90 92 ≤ 11441450937823 := by decide +kernel

theorem rows22250R_3099 : rowsJ2 115 116 92 94 ≤ 15993453541669 := by decide +kernel

theorem rows22250R_3100 : rowsJ2 115 116 94 96 ≤ 21406055096994 := by decide +kernel

theorem rows22250R_3101 : rowsJ2 115 116 96 340 ≤ 1573468288882569 := by decide +kernel

theorem rows22250R_3102 : rowsJ2 116 117 0 27 ≤ 1524908073132 := by decide +kernel

theorem rows22250R_3103 : rowsJ2 116 117 27 30 ≤ 11229530556830 := by decide +kernel

theorem rows22250R_3104 : rowsJ2 116 117 30 32 ≤ 16068397929789 := by decide +kernel

theorem rows22250R_3105 : rowsJ2 116 117 32 34 ≤ 18422762096708 := by decide +kernel

theorem rows22250R_3106 : rowsJ2 116 117 34 37 ≤ 19858385432114 := by decide +kernel

theorem rows22250R_3107 : rowsJ2 116 117 37 41 ≤ 12184183574632 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3093
#print axioms SieveCert.rows22250R_3107
