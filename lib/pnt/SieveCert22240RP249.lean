/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3002–3016 of 5066

File 249 of 387: the parts `rows22240R_3002` … `rows22240R_3016` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 92294 in units of a depth-4 test: row 105 columns 52–56, row 105
columns 57–65, row 105 columns 66–71, row 105 columns 72–75, row 105 columns 76–78, row 105 columns 79–79, row 105
columns 80–80, row 105 columns 81–81, row 105 columns 82–82, row 105 columns 83–83, row 105 columns 84–84, row 105
columns 85–85, row 105 columns 86–87, row 105 columns 88–89, row 105 columns 90–91), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3002 : rowsJ2 105 106 52 57 ≤ 375804720385 := by decide +kernel

theorem rows22240R_3003 : rowsJ2 105 106 57 66 ≤ 25296296242 := by decide +kernel

theorem rows22240R_3004 : rowsJ2 105 106 66 72 ≤ 0 := by decide +kernel

theorem rows22240R_3005 : rowsJ2 105 106 72 76 ≤ 0 := by decide +kernel

theorem rows22240R_3006 : rowsJ2 105 106 76 79 ≤ 565262943642 := by decide +kernel

theorem rows22240R_3007 : rowsJ2 105 106 79 80 ≤ 577469945201 := by decide +kernel

theorem rows22240R_3008 : rowsJ2 105 106 80 81 ≤ 880267750459 := by decide +kernel

theorem rows22240R_3009 : rowsJ2 105 106 81 82 ≤ 994485200937 := by decide +kernel

theorem rows22240R_3010 : rowsJ2 105 106 82 83 ≤ 891715172377 := by decide +kernel

theorem rows22240R_3011 : rowsJ2 105 106 83 84 ≤ 871249126878 := by decide +kernel

theorem rows22240R_3012 : rowsJ2 105 106 84 85 ≤ 949917508937 := by decide +kernel

theorem rows22240R_3013 : rowsJ2 105 106 85 86 ≤ 1070400897291 := by decide +kernel

theorem rows22240R_3014 : rowsJ2 105 106 86 88 ≤ 2851429303587 := by decide +kernel

theorem rows22240R_3015 : rowsJ2 105 106 88 90 ≤ 4276969199854 := by decide +kernel

theorem rows22240R_3016 : rowsJ2 105 106 90 92 ≤ 6323497181062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3002
#print axioms SieveCert.rows22240R_3016
