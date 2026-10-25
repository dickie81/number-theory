/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4086–4100 of 5796

File 341 of 465: the parts `rows22250R_4086` … `rows22250R_4100` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99664 tests: row 132 columns 66–66, row 132 columns 67–67, row 132 columns
68–68, row 132 columns 69–69, row 132 columns 70–70, row 132 columns 71–71, row 132 columns 72–72, row 132 columns
73–73, row 132 columns 74–74, row 132 columns 75–75, row 132 columns 76–76, row 132 columns 77–77, row 132 columns
78–78, row 132 columns 79–79, row 132 columns 80–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4086 : rowsJ2 132 133 66 67 ≤ 3924934187302 := by decide +kernel

theorem rows22250R_4087 : rowsJ2 132 133 67 68 ≤ 4214057287807 := by decide +kernel

theorem rows22250R_4088 : rowsJ2 132 133 68 69 ≤ 4463155947327 := by decide +kernel

theorem rows22250R_4089 : rowsJ2 132 133 69 70 ≤ 4653387354768 := by decide +kernel

theorem rows22250R_4090 : rowsJ2 132 133 70 71 ≤ 4802313189740 := by decide +kernel

theorem rows22250R_4091 : rowsJ2 132 133 71 72 ≤ 4890695203966 := by decide +kernel

theorem rows22250R_4092 : rowsJ2 132 133 72 73 ≤ 4936064896654 := by decide +kernel

theorem rows22250R_4093 : rowsJ2 132 133 73 74 ≤ 4918751259386 := by decide +kernel

theorem rows22250R_4094 : rowsJ2 132 133 74 75 ≤ 4856238464727 := by decide +kernel

theorem rows22250R_4095 : rowsJ2 132 133 75 76 ≤ 4209739649987 := by decide +kernel

theorem rows22250R_4096 : rowsJ2 132 133 76 77 ≤ 3615867940841 := by decide +kernel

theorem rows22250R_4097 : rowsJ2 132 133 77 78 ≤ 3054495217976 := by decide +kernel

theorem rows22250R_4098 : rowsJ2 132 133 78 79 ≤ 2543709400725 := by decide +kernel

theorem rows22250R_4099 : rowsJ2 132 133 79 80 ≤ 2063260042939 := by decide +kernel

theorem rows22250R_4100 : rowsJ2 132 133 80 82 ≤ 2859862896750 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4086
#print axioms SieveCert.rows22250R_4100
