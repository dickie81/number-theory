/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2929–2943 of 4715

File 232 of 351: the parts `rows22250R_2929` … `rows22250R_2943` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 93503 tests: row 108 columns 97–97, row 108 columns 98–98, row 108 columns
99–99, row 108 columns 100–339, row 109 columns 0–26, row 109 columns 27–30, row 109 columns 31–32, row 109 columns
33–34, row 109 columns 35–35, row 109 columns 36–37, row 109 columns 38–39, row 109 columns 40–41, row 109 columns
42–44, row 109 columns 45–49, row 109 columns 50–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2929 : rowsJ2 108 109 97 98 ≤ 10061535701815 := by decide +kernel

theorem rows22250R_2930 : rowsJ2 108 109 98 99 ≤ 11422579020130 := by decide +kernel

theorem rows22250R_2931 : rowsJ2 108 109 99 100 ≤ 12916172665423 := by decide +kernel

theorem rows22250R_2932 : rowsJ2 108 109 100 340 ≤ 909983496308998 := by decide +kernel

theorem rows22250R_2933 : rowsJ2 109 110 0 27 ≤ 231491853075 := by decide +kernel

theorem rows22250R_2934 : rowsJ2 109 110 27 31 ≤ 8526881663213 := by decide +kernel

theorem rows22250R_2935 : rowsJ2 109 110 31 33 ≤ 12267551496589 := by decide +kernel

theorem rows22250R_2936 : rowsJ2 109 110 33 35 ≤ 19911076537792 := by decide +kernel

theorem rows22250R_2937 : rowsJ2 109 110 35 36 ≤ 13797761163912 := by decide +kernel

theorem rows22250R_2938 : rowsJ2 109 110 36 38 ≤ 24148900085365 := by decide +kernel

theorem rows22250R_2939 : rowsJ2 109 110 38 40 ≤ 17631012672003 := by decide +kernel

theorem rows22250R_2940 : rowsJ2 109 110 40 42 ≤ 11511346761096 := by decide +kernel

theorem rows22250R_2941 : rowsJ2 109 110 42 45 ≤ 9341813371210 := by decide +kernel

theorem rows22250R_2942 : rowsJ2 109 110 45 50 ≤ 3011150558461 := by decide +kernel

theorem rows22250R_2943 : rowsJ2 109 110 50 61 ≤ 339494712528 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2929
#print axioms SieveCert.rows22250R_2943
