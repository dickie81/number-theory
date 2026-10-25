/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4711–4720 of 5796

File 389 of 465: the parts `rows22250R_4711` … `rows22250R_4720` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 93341 tests: row 152 columns 56–56, row 152 columns 57–57, row 152 columns
58–58, row 152 columns 59–59, row 152 columns 60–60, row 152 columns 61–61, row 152 columns 62–62, row 152 columns
63–63, row 152 columns 64–64, row 152 columns 65–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4711 : rowsJ2 152 153 56 57 ≤ 5697725339571 := by decide +kernel

theorem rows22250R_4712 : rowsJ2 152 153 57 58 ≤ 6448929101934 := by decide +kernel

theorem rows22250R_4713 : rowsJ2 152 153 58 59 ≤ 7236288217763 := by decide +kernel

theorem rows22250R_4714 : rowsJ2 152 153 59 60 ≤ 8058512365343 := by decide +kernel

theorem rows22250R_4715 : rowsJ2 152 153 60 61 ≤ 8914413663625 := by decide +kernel

theorem rows22250R_4716 : rowsJ2 152 153 61 62 ≤ 9802901744180 := by decide +kernel

theorem rows22250R_4717 : rowsJ2 152 153 62 63 ≤ 10722979250600 := by decide +kernel

theorem rows22250R_4718 : rowsJ2 152 153 63 64 ≤ 11673737740295 := by decide +kernel

theorem rows22250R_4719 : rowsJ2 152 153 64 65 ≤ 12622366307872 := by decide +kernel

theorem rows22250R_4720 : rowsJ2 152 153 65 66 ≤ 11454224054248 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4711
#print axioms SieveCert.rows22250R_4720
