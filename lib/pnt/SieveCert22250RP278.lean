/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3098–3113 of 5796

File 278 of 465: the parts `rows22250R_3098` … `rows22250R_3113` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96148 tests: row 105 columns 46–46, row 105 columns 47–47, row 105 columns
48–48, row 105 columns 49–49, row 105 columns 50–50, row 105 columns 51–52, row 105 columns 53–54, row 105 columns
55–56, row 105 columns 57–59, row 105 columns 60–64, row 105 columns 65–71, row 105 columns 72–76, row 105 columns
77–80, row 105 columns 81–82, row 105 columns 83–83, row 105 columns 84–84), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3098 : rowsJ2 105 106 46 47 ≤ 9011963292406 := by decide +kernel

theorem rows22250R_3099 : rowsJ2 105 106 47 48 ≤ 7615792358628 := by decide +kernel

theorem rows22250R_3100 : rowsJ2 105 106 48 49 ≤ 6367520359220 := by decide +kernel

theorem rows22250R_3101 : rowsJ2 105 106 49 50 ≤ 5264225833588 := by decide +kernel

theorem rows22250R_3102 : rowsJ2 105 106 50 51 ≤ 4303296312166 := by decide +kernel

theorem rows22250R_3103 : rowsJ2 105 106 51 53 ≤ 6207391249313 := by decide +kernel

theorem rows22250R_3104 : rowsJ2 105 106 53 55 ≤ 3434649788710 := by decide +kernel

theorem rows22250R_3105 : rowsJ2 105 106 55 57 ≤ 1259642267279 := by decide +kernel

theorem rows22250R_3106 : rowsJ2 105 106 57 60 ≤ 139638169000 := by decide +kernel

theorem rows22250R_3107 : rowsJ2 105 106 60 65 ≤ 0 := by decide +kernel

theorem rows22250R_3108 : rowsJ2 105 106 65 72 ≤ 0 := by decide +kernel

theorem rows22250R_3109 : rowsJ2 105 106 72 77 ≤ 0 := by decide +kernel

theorem rows22250R_3110 : rowsJ2 105 106 77 81 ≤ 49702741166 := by decide +kernel

theorem rows22250R_3111 : rowsJ2 105 106 81 83 ≤ 456952218565 := by decide +kernel

theorem rows22250R_3112 : rowsJ2 105 106 83 84 ≤ 516548382082 := by decide +kernel

theorem rows22250R_3113 : rowsJ2 105 106 84 85 ≤ 782113172809 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3098
#print axioms SieveCert.rows22250R_3113
