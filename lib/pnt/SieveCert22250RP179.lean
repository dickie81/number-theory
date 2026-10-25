/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1830–1837 of 5796

File 179 of 465: the parts `rows22250R_1830` … `rows22250R_1837` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 94989 tests: row 79 columns 51–51, row 79 columns 52–52, row 79 columns
53–53, row 79 columns 54–54, row 79 columns 55–55, row 79 columns 56–56, row 79 columns 57–57, row 79 columns
58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1830 : rowsJ2 79 80 51 52 ≤ 1651002901781 := by decide +kernel

theorem rows22250R_1831 : rowsJ2 79 80 52 53 ≤ 2117681376054 := by decide +kernel

theorem rows22250R_1832 : rowsJ2 79 80 53 54 ≤ 2444756220658 := by decide +kernel

theorem rows22250R_1833 : rowsJ2 79 80 54 55 ≤ 2590244932921 := by decide +kernel

theorem rows22250R_1834 : rowsJ2 79 80 55 56 ≤ 2741125674368 := by decide +kernel

theorem rows22250R_1835 : rowsJ2 79 80 56 57 ≤ 2709032050180 := by decide +kernel

theorem rows22250R_1836 : rowsJ2 79 80 57 58 ≤ 2528643547738 := by decide +kernel

theorem rows22250R_1837 : rowsJ2 79 80 58 59 ≤ 2350221008514 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1830
#print axioms SieveCert.rows22250R_1837
