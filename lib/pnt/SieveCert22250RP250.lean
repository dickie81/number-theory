/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3197–3212 of 4715

File 250 of 351: the parts `rows22250R_3197` … `rows22250R_3212` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97889 tests: row 120 columns 43–57, row 120 columns 58–60, row 120 columns
61–62, row 120 columns 63–64, row 120 columns 65–65, row 120 columns 66–66, row 120 columns 67–67, row 120 columns
68–68, row 120 columns 69–69, row 120 columns 70–71, row 120 columns 72–73, row 120 columns 74–76, row 120 columns
77–80, row 120 columns 81–84, row 120 columns 85–87, row 120 columns 88–89), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3197 : rowsJ2 120 121 43 58 ≤ 2041767626985 := by decide +kernel

theorem rows22250R_3198 : rowsJ2 120 121 58 61 ≤ 4698697550335 := by decide +kernel

theorem rows22250R_3199 : rowsJ2 120 121 61 63 ≤ 4859949867833 := by decide +kernel

theorem rows22250R_3200 : rowsJ2 120 121 63 65 ≤ 5710821411898 := by decide +kernel

theorem rows22250R_3201 : rowsJ2 120 121 65 66 ≤ 3018430937681 := by decide +kernel

theorem rows22250R_3202 : rowsJ2 120 121 66 67 ≤ 3032269881382 := by decide +kernel

theorem rows22250R_3203 : rowsJ2 120 121 67 68 ≤ 2991370110971 := by decide +kernel

theorem rows22250R_3204 : rowsJ2 120 121 68 69 ≤ 2870268882554 := by decide +kernel

theorem rows22250R_3205 : rowsJ2 120 121 69 70 ≤ 2691501567912 := by decide +kernel

theorem rows22250R_3206 : rowsJ2 120 121 70 72 ≤ 4533998530865 := by decide +kernel

theorem rows22250R_3207 : rowsJ2 120 121 72 74 ≤ 2775763071252 := by decide +kernel

theorem rows22250R_3208 : rowsJ2 120 121 74 77 ≤ 510578840091 := by decide +kernel

theorem rows22250R_3209 : rowsJ2 120 121 77 81 ≤ 0 := by decide +kernel

theorem rows22250R_3210 : rowsJ2 120 121 81 85 ≤ 2730408381288 := by decide +kernel

theorem rows22250R_3211 : rowsJ2 120 121 85 88 ≤ 8842266609276 := by decide +kernel

theorem rows22250R_3212 : rowsJ2 120 121 88 90 ≤ 10609916038444 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3197
#print axioms SieveCert.rows22250R_3212
