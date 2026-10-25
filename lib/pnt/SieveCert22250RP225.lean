/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2819–2833 of 4715

File 225 of 351: the parts `rows22250R_2819` … `rows22250R_2833` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98691 tests: row 105 columns 46–48, row 105 columns 49–53, row 105 columns
54–63, row 105 columns 64–70, row 105 columns 71–74, row 105 columns 75–77, row 105 columns 78–79, row 105 columns
80–80, row 105 columns 81–81, row 105 columns 82–83, row 105 columns 84–85, row 105 columns 86–87, row 105 columns
88–89, row 105 columns 90–91, row 105 columns 92–93), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_2819 : rowsJ2 105 106 46 49 ≤ 4813205364840 := by decide +kernel

theorem rows22250R_2820 : rowsJ2 105 106 49 54 ≤ 479255247533 := by decide +kernel

theorem rows22250R_2821 : rowsJ2 105 106 54 64 ≤ 0 := by decide +kernel

theorem rows22250R_2822 : rowsJ2 105 106 64 71 ≤ 0 := by decide +kernel

theorem rows22250R_2823 : rowsJ2 105 106 71 75 ≤ 0 := by decide +kernel

theorem rows22250R_2824 : rowsJ2 105 106 75 78 ≤ 343173699019 := by decide +kernel

theorem rows22250R_2825 : rowsJ2 105 106 78 80 ≤ 1161721257565 := by decide +kernel

theorem rows22250R_2826 : rowsJ2 105 106 80 81 ≤ 823009938105 := by decide +kernel

theorem rows22250R_2827 : rowsJ2 105 106 81 82 ≤ 727557750954 := by decide +kernel

theorem rows22250R_2828 : rowsJ2 105 106 82 84 ≤ 1217269969616 := by decide +kernel

theorem rows22250R_2829 : rowsJ2 105 106 84 86 ≤ 1368439208631 := by decide +kernel

theorem rows22250R_2830 : rowsJ2 105 106 86 88 ≤ 2110375448481 := by decide +kernel

theorem rows22250R_2831 : rowsJ2 105 106 88 90 ≤ 3469891850067 := by decide +kernel

theorem rows22250R_2832 : rowsJ2 105 106 90 92 ≤ 5474000712162 := by decide +kernel

theorem rows22250R_2833 : rowsJ2 105 106 92 94 ≤ 8154099963876 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2819
#print axioms SieveCert.rows22250R_2833
