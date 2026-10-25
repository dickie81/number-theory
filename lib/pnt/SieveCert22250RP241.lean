/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3064–3078 of 4715

File 241 of 351: the parts `rows22250R_3064` … `rows22250R_3078` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99300 tests: row 114 columns 43–51, row 114 columns 52–61, row 114 columns
62–64, row 114 columns 65–67, row 114 columns 68–71, row 114 columns 72–74, row 114 columns 75–77, row 114 columns
78–80, row 114 columns 81–83, row 114 columns 84–86, row 114 columns 87–89, row 114 columns 90–91, row 114 columns
92–93, row 114 columns 94–95, row 114 columns 96–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3064 : rowsJ2 114 115 43 52 ≤ 1120772145447 := by decide +kernel

theorem rows22250R_3065 : rowsJ2 114 115 52 62 ≤ 2813077687433 := by decide +kernel

theorem rows22250R_3066 : rowsJ2 114 115 62 65 ≤ 3269503848728 := by decide +kernel

theorem rows22250R_3067 : rowsJ2 114 115 65 68 ≤ 2529273937014 := by decide +kernel

theorem rows22250R_3068 : rowsJ2 114 115 68 72 ≤ 354733464319 := by decide +kernel

theorem rows22250R_3069 : rowsJ2 114 115 72 75 ≤ 0 := by decide +kernel

theorem rows22250R_3070 : rowsJ2 114 115 75 78 ≤ 14188532890 := by decide +kernel

theorem rows22250R_3071 : rowsJ2 114 115 78 81 ≤ 0 := by decide +kernel

theorem rows22250R_3072 : rowsJ2 114 115 81 84 ≤ 699625289110 := by decide +kernel

theorem rows22250R_3073 : rowsJ2 114 115 84 87 ≤ 4016857656616 := by decide +kernel

theorem rows22250R_3074 : rowsJ2 114 115 87 90 ≤ 9615528914715 := by decide +kernel

theorem rows22250R_3075 : rowsJ2 114 115 90 92 ≤ 10707536738482 := by decide +kernel

theorem rows22250R_3076 : rowsJ2 114 115 92 94 ≤ 15052491455004 := by decide +kernel

theorem rows22250R_3077 : rowsJ2 114 115 94 96 ≤ 20231841281394 := by decide +kernel

theorem rows22250R_3078 : rowsJ2 114 115 96 97 ≤ 12328367412558 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3064
#print axioms SieveCert.rows22250R_3078
